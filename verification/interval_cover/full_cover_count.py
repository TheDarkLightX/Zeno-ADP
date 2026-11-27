"""Minimum cost and exact number of distinct minimum-cost interval subsets."""
from itertools import combinations
from random import Random

def choice(a,b):
    if a is None or b is None:
        return b if a is None else a
    if a[0]!=b[0]:
        return min(a,b)
    return a[0],a[1]+b[1]

class Chart:
    """Range choice plus lazy tie-count doubling, with explicit empty score."""
    def __init__(self,n):
        self.n=1<<(n-1).bit_length()
        self.cell=[None]*(2*self.n)
        self.pow=[0]*(2*self.n)

    def scale(self,k,shift):
        if self.cell[k] is not None:
            c,t=self.cell[k]
            self.cell[k]=c,t<<shift
            self.pow[k]+=shift

    def push(self,k):
        sh=self.pow[k]
        if sh==-1:
            for j in (2*k,2*k+1):
                self.cell[j]=None
                self.pow[j]=-1
        elif sh:
            self.scale(2*k,sh)
            self.scale(2*k+1,sh)
        self.pow[k]=0

    def clear_prefix(self,end):
        def go(k,l,r):
            if end<=l or self.cell[k] is None:return
            if r<=end:
                self.cell[k]=None
                self.pow[k]=-1
                return
            self.push(k)
            m=(l+r)//2
            go(2*k,l,m)
            go(2*k+1,m,r)
            self.cell[k]=choice(self.cell[2*k],self.cell[2*k+1])
        go(1,0,self.n)

    def point(self,i,v,combine):
        def go(k,l,r):
            if r-l==1:
                self.cell[k]=choice(self.cell[k],v) if combine else v
                self.pow[k]=0
                return
            self.push(k)
            m=(r+l)//2
            if i<m:
                go(k*2,l,m)
            else:
                go(k*2+1,m,r)
            self.cell[k]=choice(self.cell[2*k],self.cell[2*k+1])
        go(1,0,self.n)

    def prefix(self,end):
        def go(k,l,r):
            if end<=l:return None
            if r<=end:return self.cell[k]
            self.push(k)
            m=(l+r)//2
            return choice(go(2*k,l,m),go(2*k+1,m,r))
        return go(1,0,self.n)

    def double_suffix(self,start):
        def go(k,l,r):
            if r<=start or self.cell[k] is None:return
            if start<=l:
                self.scale(k,1)
                return
            self.push(k)
            m=(l+r)//2
            go(2*k,l,m)
            go(2*k+1,m,r)
            self.cell[k]=choice(self.cell[2*k],self.cell[2*k+1])
        go(1,0,self.n)

def solve(n,rows,*,required=(),banned=()):
    """Rows are labelled by their position. Endpoints are inclusive."""
    req,ban=set(required),set(banned)
    if req&ban:
        return None
    if not (req|ban)<=set(range(len(rows))):
        raise ValueError('invalid row id')
    by_left=[[] for _ in range(n)]
    fixed=0
    for i,(l,r,w) in enumerate(rows):
        if not 0<=l<=r<n or w<0:
            raise ValueError('invalid interval or negative price')
        if i in ban:
            continue
        if i in req:
            fixed+=w
        by_left[l].append((r+1,w,i in req))
    c=Chart(n+1)
    c.point(0,(fixed,1),False)
    # Required guards cover for free in the recurrence with no skip branch.
    # Their presence may make several old frontier states merge at r.
    # The baseline O(log n) per optional row remains; range clear handles pins.
    for l,events in enumerate(by_left):
        for r,w,mandatory in events:
            partial=c.prefix(r)
            if mandatory:
                c.clear_prefix(r)
            elif w==0:
                c.double_suffix(r)
            if partial is not None:
                c.point(r,(partial[0]+(0 if mandatory else w),partial[1]),True)
        c.point(l,None,False)
    return c.cell[1]

def exhaustive(n,rows,req=(),ban=()):
    best=None
    m=len(rows)
    eligible=set(range(m))-set(ban)
    for k in range(len(eligible)+1):
        for ids in combinations(eligible,k):
            if not set(req)<=set(ids):continue
            if not all(any(rows[i][0]<=x<=rows[i][1] for i in ids) for x in range(n)):
                continue
            best=choice(best,(sum(rows[i][2] for i in ids),1))
    return best

def full_reference(n,rows,req=(),ban=()):
    s={0:(0,1)}
    for x in range(n):
        for i,(l,r,w) in enumerate(rows):
            if l!=x or i in ban:continue
            t=dict(s) if i not in req else {}
            for q,v in s.items():
                h=max(q,r+1)
                t[h]=choice(t.get(h),(v[0]+w,v[1]))
            s=t
        s.pop(x,None)
    return s.get(n)

def main():
    rng=Random(9331)
    tested=pins=0
    for _ in range(1200):
        n=rng.randrange(1,8)
        rows=[]
        for i in range(rng.randrange(11)):
            l=rng.randrange(n)
            rows.append((l,rng.randrange(l,n),rng.randrange(4)))
        assert solve(n,rows)==exhaustive(n,rows)==full_reference(n,rows)
        tested+=1
        for _ in range(4):
            req={i for i in range(len(rows)) if rng.randrange(5)==0}
            ban={i for i in range(len(rows)) if i not in req and rng.randrange(5)==0}
            assert solve(n,rows,required=req,banned=ban)==exhaustive(n,rows,req,ban)==full_reference(n,rows,req,ban)
            pins+=1
    assert solve(1,[(0,0,0)]*1000)==(0,2**1000-1)
    assert solve(120,[(i,i,1) for i in range(120) for _ in range(3)])==(120,3**120)
    assert solve(50_000,[(i,i,0) for i in range(50_000) for _ in range(3)])==(0,7**50_000)
    print(f'{tested} exhaustive menus; {pins} pinned cases; exact 2^1000-1, 3^120, 7^50000 controls')
if __name__=='__main__':
    main()
