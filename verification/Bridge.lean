import BellmanAlgebras
import BellmanLexicographic
import IntervalConvolution

open Lean BellmanTabulation
open BellmanAlgebras (Summary)

structure EncodedRule where
  id : Nat
  arity : Nat
  cost : Option Int
  secondary : Int
  children : List Nat
  deriving FromJson

structure Input where
  group : String
  root : Nat
  dimensions : Option (Array Int)
  cells : Array (List EncodedRule)
  deriving FromJson

def decodeChart (input : Input) (finite := false) : Chart EncodedRule := fun rank =>
  (input.cells[rank]?.getD []).filterMap fun rule => do
    if finite && rule.cost.isNone then none else
      let children ← rule.children.mapM fun child =>
        if h : child < rank then some (⟨child, h⟩ : Fin rank) else none
      pure (rule, children)

private def validate (input : Input) : Except String Unit := do
  if input.root ≥ input.cells.size then throw "root outside chart"
  for rank in [:input.cells.size] do
    for rule in input.cells[rank]! do
      if rule.arity != rule.children.length then throw s!"invalid arity at rank {rank}"
      if rule.children.any (· ≥ rank) then throw s!"non-descending child at rank {rank}"

private def treeJson : Tree EncodedRule → Json
  | .node op children => .arr #[toJson op.id, .arr (children.map treeJson).toArray]

private def summaryJson : Summary → Json
  | .finite c opt total => .arr #[toJson c, toJson opt, toJson total]
  | .infinity total => .arr #[.null, toJson total, toJson total]

private def lexJson (s : BellmanLexicographic.Score) : Json :=
  .arr #[toJson s.primary, toJson s.secondary]

private def matrixCells (dims : Array Int) : List (Option Int) :=
  letI := IntervalConvolution.minPlusSemiring
  let n := dims.size - 1
  (List.range n).flatMap fun widthMinusOne =>
    (List.range (n - widthMinusOne)).map fun left =>
      IntervalConvolution.intervalDP (fun _ => some 0)
        (fun i k j => some (dims[i]! * dims[k]! * dims[j]!)) left widthMinusOne

def evaluate (input : Input) : Except String Json := do
  validate input
  let size := input.cells.size
  let chart := decodeChart input
  let counts := tabulate chart BellmanAlgebras.countApply BellmanAlgebras.countChoose size
  let terms := tabulate chart Tree.node id size
  let ties := tabulate chart (BellmanAlgebras.tiesApply EncodedRule.cost)
    BellmanAlgebras.tiesChoose size
  let minimum := tabulate chart (BellmanAlgebras.minimumApply EncodedRule.cost)
    BellmanAlgebras.minimumChoose size
  let lex := tabulate (decodeChart input true)
    (BellmanLexicographic.apply
      (fun op => ⟨op.cost.getD 0, op.secondary⟩))
    BellmanLexicographic.choose size
  let cells := (List.range size).map fun rank =>
    Json.arr #[
      toJson (lookup counts rank),
      toJson ((lookup terms rank).map treeJson),
      toJson ((lookup ties rank).map summaryJson),
      toJson (lookup minimum rank),
      toJson ((lookup lex rank).map lexJson)]
  if let some dims := input.dimensions then
    if (matrixCells dims).map (fun cost => [cost]) != minimum then
      throw "interval model disagrees with the ranked matrix chart"
  pure (.arr #[toJson input.group, toJson input.root, toJson cells])

def main (args : List String) : IO Unit := do
  let reverse ← match args with
    | [] => pure false
    | ["reverse"] => pure true
    | _ => throw (IO.userError "expected no flags or reverse")
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut lineNumber := 0
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    lineNumber := lineNumber + 1
    let result := do
      let row ← (Json.parse line).bind (fromJson? (α := Input))
      let row := if reverse then { row with cells := row.cells.map List.reverse } else row
      evaluate row
    match result with
    | .ok answers => output.putStrLn answers.compress
    | .error message => throw (IO.userError s!"input line {lineNumber}: {message}")
