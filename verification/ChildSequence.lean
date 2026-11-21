namespace ChildSequence

/-- Preflight optional child summaries and expose the ordered inhabited list. -/
def project (children : List (Option α)) : Option (List α) :=
  if children.all Option.isSome then some (children.filterMap id) else none

theorem project_enabled (values : List α) :
    project (values.map some) = some values := by
  simp [project, List.all_map, List.filterMap_map, Function.comp_def]

theorem project_disabled (children : List (Option α))
    (missing : children.all Option.isSome = false) :
    project children = none := by
  simp [project, missing]

theorem remaining_count (values : List α) (consumed : Nat) :
    (project (values.map some)).map (fun xs => (xs.drop consumed).length) =
      some (values.length - consumed) := by
  simp [project_enabled]

end ChildSequence
