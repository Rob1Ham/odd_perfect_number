"""Emit interval certificates for the residual 3-smooth branch of Cohen–Sorli."""

import argparse
from array import array
from collections import Counter
from functools import cache
from math import gcd, isqrt, lcm, prod
from pathlib import Path

from harmonic_chain import COMPONENT_BOUND, SIZE_BOUND, prime_factors
from count_chain import Factorer

proof_factorer = Factorer(15)
proof_factorer.full = cache(proof_factorer.full)

LENGTHS = (1, 2, 3, 5, 7, 8, 11, 15, 17, 23, 26, 31)
STRIP = 6**128


@cache
def exponents(p):
    return tuple(e for e in LENGTHS if p**e < COMPONENT_BOUND and p**e % 4 == 1)


def integer_root(n, degree):
    low, high = 0, 1
    while high**degree <= n:
        high *= 2
    while low + 1 < high:
        mid = (low+high)//2
        if mid**degree <= n:
            low = mid
        else:
            high = mid
    return low


def witnesses(limit):
    table = array('H', [0])*limit
    for p in range(2,isqrt(limit-1)+1):
        if table[p]:
            continue
        for j in range(p*p,limit,p):
            if not table[j]:
                table[j] = p
    return table


def pairs(entries):
    return '['+', '.join(f'({k},{value})' for k,value in entries)+']'


class Search:
    def __init__(self):
        self.primes = {2,3}
        self.nodes = Counter()
        self.max_depth = 0

    def children(self,path,ban,p,r,depth):
        result = []
        for e in exponents(p):
            if (e+1) % r:
                continue
            t = self.visit(path+[(p,e)],ban,depth+1)
            if t != '.done':
                result.append((e,t))
        return pairs(result)

    def visit(self,path,ban,depth):
        self.max_depth = max(self.max_depth,depth)
        self.nodes['states'] += 1
        fixed = dict(path)
        D = prod(p**e for p,e in path)
        sigmas = [(p**(e+1)-1)//(p-1) for p,e in path]
        S = prod(sigmas)
        c = S//gcd(S,STRIP)
        U = lcm(D,c)
        if gcd(c,6)!=1:
            raise ValueError("insufficient stripping power")
        if U>SIZE_BOUND or gcd(D,c//gcd(D,c))!=1:
            return '.done'
        need = Counter(p for value in sigmas for p in prime_factors(value) if p>3)
        if prod(p**v for p,v in need.items())!=c:
            raise ValueError("incomplete proposal for the stripped divisor sum")
        raised = []
        for p,e in sorted(need.items(),reverse=True):
            if p%4==3 and e%2 and fixed.get(p,0)<=e:
                U = lcm(U,p**(e+1))
                raised.append((p,e))
                if U>SIZE_BOUND:
                    self.primes.update(q for q,_ in raised)
                    return '(.raise '+pairs(raised)+')'
        required = {p:e+int(p%4==3 and e%2==1) for p,e in need.items() if p not in fixed}
        for p,e in required.items():
            if p**e>=COMPONENT_BOUND:
                self.primes.add(p)
                zs = [(p,e-1)] if need[p]<e else []
                return f'(.component {p} {e} {pairs(zs)})'
        if required:
            p = max(required,key=lambda q:q**required[q])
            self.primes.add(p)
            return f'(.split {p} {self.children(path,ban,p,1,depth)})'
        T = prod(e+1 for p,e in path)
        v = S//gcd(S,D*T)
        if 3 not in fixed and not ban and v%3==0:
            absent = self.visit(path,True,depth+1)
            return f'(.three {absent} {self.children(path,False,3,1,depth)})'
        possibilities = []
        for r in (2,3):
            if v%r:
                continue
            a,w = 0,v
            while w%r==0:
                a,w = a+1,w//r
            L = 1+integer_root(SIZE_BOUND//D,(r-1)*a)
            possibilities.append((L,r,a))
        if not possibilities:
            raise ValueError(f"unresolved prefix {path}")
        L,r,b = min(possibilities)
        if L>5000:
            raise ValueError(f"large residual interval at {path}: {L}")
        children = []
        for q in range(3,L,2):
            if q in fixed or (ban and q==3) or prime_factors(q)!=(q,):
                continue
            cs = self.children(path,ban,q,r,depth)
            if cs!='[]':
                children.append((q,cs))
        return f'(.owed {r} {b} {L} {pairs(children)})'


@cache
def prime_proof(p):
    return proof_factorer.prime_proof(p)


def bank_defs(P,tag):
    primes = sorted(P)
    groups = []
    blocks = []
    for i in range(0,len(primes),16):
        ps = primes[i:i+16]
        name = f'leaf{tag}_{i//16}'
        cert = ', '.join(prime_proof(p) for p in ps)
        blocks.extend([f'@[expose] def {name} : PrimeBank := .leaf {ps}',
                       f'theorem {name}_valid : {name}.Certified := by',
                       f'  simp only [{name},PrimeBank.Certified,List.forall_mem_cons]',
                       f'  exact ⟨{cert}, by simp⟩',''])
        groups.append((ps[0],name))

    def balanced(parts):
        if len(parts)==1:
            return parts[0][1],parts[0][1]+'_valid'
        j=len(parts)//2
        l,lc=balanced(parts[:j]);r,rc=balanced(parts[j:])
        return f'(.branch {parts[j][0]} {l} {r})',f'⟨{lc},{rc}⟩'
    value,proof=balanced(groups)
    blocks.extend([f'@[expose] def pool{tag} : PrimeBank := {value}',
                   f'theorem pool{tag}_valid : pool{tag}.Certified := {proof}',''])
    return blocks


@cache
def order_row(p):
    if p < 512:
        return 0, []
    powers = Counter(proof_factorer.full(p-1))
    F, factors = 1, []
    for q,e in sorted(powers.items(),key=lambda pair:pair[0]**pair[1],reverse=True):
        F *= q**e
        factors.append((q,e))
        if p < (F+1)**2:
            break
    for a in range(2,p):
        b = pow(a,(p-1)//F,p)
        if pow(b,F,p)==1 and all(gcd(pow(b,F//q,p)-1,p)==1 for q,_ in factors):
            return b, factors
    raise ValueError(f"No order witness for {p}")


def order_bank_defs(P,tag):
    rows = {}
    def collect(p):
        if p in rows:
            return
        b, factors = order_row(p)
        rows[p] = (b, factors)
        for q,_ in factors:
            if q>=512:
                collect(q)
    for p in P:
        collect(p)
    ordered = sorted(rows)
    blocks, leaves = [], []
    for i in range(0,len(ordered),12):
        ps=ordered[i:i+12]
        name=f'orders{tag}_{i//12}'
        data=', '.join(f'({p},{rows[p][0]},{pairs(rows[p][1])})' for p in ps)
        blocks.append(f'@[expose] def {name} : OrderTable := .leaf [{data}]')
        leaves.append((ps[0],name))
    def balanced(xs):
        if len(xs)==1:
            return xs[0][1]
        j=len(xs)//2
        return f'(.branch {xs[j][0]} {balanced(xs[:j])} {balanced(xs[j:])})'
    blocks.extend(['',f'@[expose] def orderTable{tag} : OrderTable := {balanced(leaves)}',
                  f'@[expose] def pool{tag} : PrimeBank := orderTable{tag}.bank',
                  f'theorem pool{tag}_valid : pool{tag}.Certified :=',
                  f'  orderTable{tag}.certified_of_check (by decide +kernel)',''])
    return blocks


def emit(low,high,directory,per_module,width,order_table=False):
    assert 3<=low<high<=1316099 and low%2 and high%2
    directory.mkdir(parents=True,exist_ok=True)
    spf=witnesses(high)
    previous='OddPerfect.HarmonicRange'
    namespace=directory.name
    total=Counter()
    for module,start in enumerate(range(low,high,2*per_module),1):
        stop=min(high,start+2*per_module)
        search=Search()
        blocks=[]
        names=[]
        for a in range(start,stop,2*width):
            b=min(stop,a+2*width)
            divs=[];roots=[]
            for p in range(a,b,2):
                if spf[p]:
                    divs.append(spf[p]);continue
                tree=search.children([],False,p,3,0)
                if tree=='[]':divs.append(1)
                else:divs.append(0);roots.append(tree)
            name=f'covered{a}'
            pack=f'[{", ".join(roots)}]'
            fuel=search.max_depth+2
            blocks.extend([f'theorem {name} : Range {a} {b} :=',
                           f'  scan_sound pool{start} pool{start}_valid {fuel} {a} {divs} {pack}',
                           '    (by decide) (by decide +kernel)',''])
            names.append(name)
        def join(ns):
            if len(ns)==1:return ns[0]
            k=len(ns)//2
            return f'(range_join {join(ns[:k])} {join(ns[k:])})'
        aggregate=f'segment{start}'
        blocks.extend([f'theorem {aggregate} : Range {start} {stop} := {join(names)}',''])
        if start>low:aggregate=f'(range_join through{start} {aggregate})'
        blocks.extend([f'theorem through{stop} : Range {low} {stop} := {aggregate}',''])
        imports = 'public import OddPerfect.OrderTable' if order_table else 'import Mathlib.Tactic.Primality'
        bank = order_bank_defs if order_table else bank_defs
        lines=['module','',f'public import {previous}',imports,'',
               'public section','',f'namespace OddPerfect.HarmonicChain.{namespace}','',
               'set_option maxRecDepth 20000','set_option maxHeartbeats 0','',
               *bank(search.primes,start),*blocks,f'end OddPerfect.HarmonicChain.{namespace}','']
        name=f'Part{module:03d}'
        (directory/f'{name}.lean').write_text('\n'.join(lines))
        total.update(search.nodes)
        previous=f'OddPerfect.{namespace}.{name}'
        print(previous,stop,dict(total),len(search.primes),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('low',type=int)
    parser.add_argument('high',type=int)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--per-module',type=int,default=2048)
    parser.add_argument('--width',type=int,default=48)
    parser.add_argument('--order-table',action='store_true')
    a=parser.parse_args()
    emit(a.low,a.high,a.output,a.per_module,a.width,a.order_table)
