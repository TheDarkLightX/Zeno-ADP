"""Inside/outside for exact count and single-row interventions, no numeric pruning."""
from itertools import combinations
from random import Random
from full_cover_count import choice, exhaustive

def mul(a,b):
    return None if a is None or b is None else (a[0]+b[0],a[1]*b[1])

class Tape:
    def __init__(self):
        self.nodes=[None,None]
        self.values=[None,(0,1)]

    def leaf(self,v):
        self.nodes.append(None)
        self.values.append(v)
        return len(self.nodes)-1

    def op(self,is_mul,a,b):
        # Only prune structural zero or unit, never equal evaluated values.
        if is_mul:
            if not a or not b:return 0
            if a==1 or b==1:return b if a==1 else a
            f=mul
        else:
            if not a or not b:return a or b
            f=choice
        self.nodes.append((is_mul,a,b))
        self.values.append(f(self.values[a],self.values[b]))
        return len(self.nodes)-1

    def outside(self,root):
        d=[None]*len(self.nodes)
        d[root]=(0,1)
        for i in range(root,1,-1):
            g=self.nodes[i]
            if d[i] is None or g is None:continue
            is_mul,a,b=g
            if is_mul:
                d[a]=choice(d[a],mul(d[i],self.values[b]))
                d[b]=choice(d[b],mul(d[i],self.values[a]))
            else:
                d[a]=choice(d[a],d[i])
                d[b]=choice(d[b],d[i])
        return d

class Tree:
    def __init__(self,n,tape):
        self.n=1<<(n-1).bit_length()
        self.a=[0]*(2*self.n)
        self.lazy=[1]*(2*self.n)
        self.t=tape
    def apply(self,k,g):
        if self.a[k]:
            self.a[k]=self.t.op(True,self.a[k],g)
            self.lazy[k]=self.t.op(True,self.lazy[k],g)
    def push(self,k):
        if self.lazy[k]!=1:
            self.apply(k*2,self.lazy[k])
            self.apply(k*2+1,self.lazy[k])
            self.lazy[k]=1
    def update(self,k):
        self.a[k]=self.t.op(False,self.a[k*2],self.a[k*2+1])
    def range_mul(self,start,end,g):
        def go(k,l,r):
            if r<=start or end<=l or not self.a[k]:return
            if start<=l and r<=end:
                self.apply(k,g)
                return
            self.push(k)
            m=(r+l)//2
            go(k*2,l,m)
            go(k*2+1,m,r)
            self.update(k)
        go(1,0,self.n)
    def prefix(self,end):
        def go(k,l,r):
            if end<=l or not self.a[k]:return 0
            if r<=end:return self.a[k]
            self.push(k)
            m=(r+l)//2
            return self.t.op(False,go(k*2,l,m),go(k*2+1,m,r))
        return go(1,0,self.n)
    def point(self,i,v,combine):
        def go(k,l,r):
            if r-l==1:
                self.a[k]=self.t.op(False,self.a[k],v) if combine else v
                self.lazy[k]=1
                return
            self.push(k)
            m=(r+l)//2
            if i<m:go(k*2,l,m)
            else:go(k*2+1,m,r)
            self.update(k)
        go(1,0,self.n)

def analyze(n,rows,req=frozenset(),ban=frozenset()):
    if req&ban:raise ValueError('contradictory pins')
    if not (req|ban)<=set(range(len(rows))):raise ValueError('unknown row id')
    tape=Tape()
    tree=Tree(n+1,tape)
    tree.point(0,1,False)
    events=[[] for _ in range(n)]
    labels=[None]*len(rows)
    for i,(l,r,w) in enumerate(rows):
        if not 0<=l<=r<n or w<0:raise ValueError('bad interval')
        s=0 if i in req else tape.leaf((0,1))
        t=0 if i in ban else tape.leaf((w,1))
        labels[i]=s,t
        events[l].append((r+1,s,t))
    for l,group in enumerate(events):
        for r,s,t in group:
            a=tape.op(True,tree.prefix(r),t)
            tree.range_mul(0,r,s)
            tree.range_mul(r,n+1,tape.op(False,s,t))
            tree.point(r,a,True)
        tree.point(l,0,False)
    root=tree.a[1]
    d=tape.outside(root)
    per=[(mul(d[s],tape.values[s]),mul(d[t],tape.values[t])) for s,t in labels]
    best=tape.values[root]
    if best is None:
        return None,per,None,len(tape.nodes)
    # Only publish coordinates that agree across every optimum.
    agreed={}
    for i,(off,on) in enumerate(per):
        if off==best:agreed[i]=False
        elif on==best:agreed[i]=True
    return best,per,agreed,len(tape.nodes)

def main():
    rng=Random(93031)
    N=raises=pin_pairs=0
    for _ in range(950):
        n=rng.randrange(1,8)
        rows=[]
        for _ in range(rng.randrange(10)):
            l=rng.randrange(n)
            rows.append((l,rng.randrange(l,n),rng.randrange(5)))
        for pin in (False,True):
            req=set();ban=set()
            if rows and pin:
                (req if rng.randrange(2) else ban).add(rng.randrange(len(rows)))
            optimal,cf,a,_=analyze(n,rows,req,ban)
            assert optimal==exhaustive(n,rows,req,ban)
            want={}
            for i,(off,on) in enumerate(cf):
                assert off==(None if i in req else exhaustive(n,rows,req,ban|{i}))
                assert on==(None if i in ban else exhaustive(n,rows,req|{i},ban))
                assert choice(off,on)==optimal
                if optimal is not None:
                    if off==optimal:want[i]=False
                    if on==optimal:want[i]=True
                    raises+=sum(q is not None and q[0]>optimal[0] for q in (off,on))
                N+=2
                pin_pairs+=2*pin
                if not pin and on is not None:
                    # Changing only the take price translates that slice.
                    w=rng.randrange(6)
                    l,r,old=rows[i]
                    changed=rows[:];changed[i]=(l,r,w)
                    assert choice(off,(on[0]+w-old,on[1]))==exhaustive(n,changed)
            assert a==(None if optimal is None else want)
    n=2000
    b,p,a,g=analyze(n,[(i,i,0) for i in range(n) for _ in range(3)])
    k=7**(n-1)
    assert b==(0,7*k) and a=={} and all(x==((0,3*k),(0,4*k)) for x in p)
    assert analyze(1,[(0,0,1),(0,0,5)])[1][1][1]==(5,1)
    print(f'{N} conditional answers ({pin_pairs} with baseline pins); {raises} raised optima; 6000-row control, {g} gates')
if __name__=='__main__':
    main()
