"""Generate independent Lean factor chains for primes in the divisor count of an odd harmonic number."""

import argparse
from collections import Counter
from dataclasses import dataclass
from functools import cache
from math import lcm, prod
from pathlib import Path

from count_chain import Factorer

COMPONENT_BOUND = 10**15
SIZE_BOUND = 10**24
factorer = Factorer(15)
decide = "(by decide +kernel)"


@cache
def prime_factors(n):
    if n <= 1:
        return ()
    if n < 20000:
        d = 2
        while d*d <= n:
            if n % d == 0:
                return (d, *prime_factors(n//d))
            d += 1
        return (n,)
    return tuple(factorer.full(n))


def powers(p):
    e, value = 1, p
    while value < COMPONENT_BOUND:
        if value % 4 == 1:
            yield e
        e, value = e+1, value*p


def power_cutoff(p):
    e = 1
    while p**e < COMPONENT_BOUND:
        e += 1
    return e


def state(path):
    return (prod(p**e for p,e in path),
            prod((p**(e+1)-1)//(p-1) for p,e in path),
            sum(e for _,e in path), len(path))


@dataclass
class Case:
    name: str
    head: str
    body: list


class Chain:
    def __init__(self, r):
        self.r = r
        self.proofs = []
        self.primes = set()
        self.counts = Counter()

    def prime(self,p):
        if p < 32:
            return "(by norm_num)"
        self.primes.add(p)
        return f"htauPrime{self.r}_{p}"

    def raises(self,items):
        if not items:
            return "[]", "(by simp)"
        literal = "["+",".join(f"({p},{e})" for p,e in items)+"]"
        alts = "|".join("rfl" for _ in items)
        # Newlines put each alternative in its own tactic block.
        witness = ("(by\n    intro z hz\n    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz\n"
                   + f"    rcases hz with {alts}\n" + "\n".join("    · exact "+self.prime(p) for p,_ in items)+")")
        return literal,witness

    def exponent_cases(self,p,r,children,indent="  "):
        exps=list(children)
        literal=str(exps)
        E=power_cutoff(p)
        hd="hdiv" if r != 1 else "(one_dvd _)"
        lines=[f"{indent}have cases := allowed_list (p:={p}) (r:={r}) (E:={E}) {literal} "
               f"(by decide) {decide} {decide} he {hd}",
               indent+"simp only [List.mem_cons,List.not_mem_nil,or_false] at cases"]
        if not exps:
            return lines+[indent+"exact cases.elim"]
        lines.append(indent+"rcases cases with "+"|".join("rfl" for _ in exps))
        lines.extend(indent+"· exact "+child for child in children.values())
        return lines

    def visit(self,path):
        D,S,spent,count=state(path)
        fixed=dict(path)
        need=Counter(p for q,e in path for p in prime_factors((q**(e+1)-1)//(q-1)) if p>self.r)
        c=prod(p**e for p,e in need.items())
        U=lcm(D,c)
        raised=sorted(((p,e) for p,e in need.items() if p%4==3 and e%2 and
                       fixed.get(p,0)<=e),reverse=True)
        choices=[(p,e+(p%4==3 and e%2==1)) for p,e in need.items() if p not in fixed]
        short=next(((p,fixed[p]+1) for p,e in need.items() if p in fixed and fixed[p]<e),None)
        node=f"⟨{D},{S},{spent},{count}⟩"
        prefix=f"(c:={c})"
        def save(kind,body):
            name=f"htau{self.r}_{len(self.proofs)}"
            self.counts[kind]+=1
            self.proofs.append(Case(name, f"Closed {self.r} {node}",body))
            return name

        if short:
            p,e=short
            return save("exact",[f"  exact closed_exact {prefix} (p:={p}) (e:={e}) {decide} {decide} "
                                 f"{self.prime(p)} {decide} {decide} {decide}"])
        used=[]
        for p,e in raised:
            if U>SIZE_BOUND:break
            U=lcm(U,p**(e+1))
            used.append((p,e))
        if U>SIZE_BOUND:
            items,witness=self.raises(used)
            return save("size",[f"  exact closed_size {prefix} {items} {decide} {decide} {witness} {decide}"])
        for p,e in choices:
            if p**e >= COMPONENT_BOUND:
                items,witness=self.raises([(p,e-1)] if need[p]<e else [])
                return save("component",[f"  exact closed_component {prefix} (p:={p}) (e:={e}) {items} "
                            f"{decide} {decide} {witness} {self.prime(p)} (by decide) {decide} {decide}"])
        if not choices:
            raise ValueError(f"uncovered branch for largest divisor-count prime {self.r}: {path}")
        p=max(choices,key=lambda pe:pe[0]**pe[1])[0]
        children={e:self.visit(path+[(p,e)]) for e in powers(p)}
        return save("split",[f"  apply closed_split {prefix} (p:={p}) {decide} {decide} "
                             f"{self.prime(p)} {decide} {decide}",
                             "  intro e he",*self.exponent_cases(p,1,children)])

    def generate(self):
        q=3
        roots={}
        while q**(self.r-1)<COMPONENT_BOUND:
            if prime_factors(q)==(q,):
                children={e:self.visit([(q,e)]) for e in powers(q) if (e+1)%self.r==0}
                name=f"htauRoot{self.r}_{q}"
                self.proofs.append(Case(name,f"RootAt {self.r} {q}",
                    ["  intro e he hdiv",*self.exponent_cases(q,self.r,children)]))
                roots[q]=name
            q+=1
        M=q
        blocks=[]
        for a in range(3,M,80):
            b=min(a+80,M)
            primes=[p for p in roots if a<=p<b]
            witnesses=[0 if i in roots else prime_factors(i)[0] for i in range(a,b)]
            body=["  intro p hlo hhi hp",
                  f"  have pm := prime_mem_of_witnesses (a:={a}) {primes} {witnesses} {decide} hp hlo hhi",
                  "  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm"]
            if primes:
                body.append("  rcases pm with "+"|".join("rfl" for _ in primes))
                body.extend("  · exact "+roots[p] for p in primes)
            else:
                body.append("  exact pm.elim")
            name=f"htauRange{self.r}_{a}"
            self.proofs.append(Case(name,f"RootRange {self.r} {a} {b}",body))
            blocks.append(name)
        while len(blocks)>1:
            blocks=[f"(root_join {blocks[k]} {blocks[k+1]})" if k+1<len(blocks) else blocks[k]
                    for k in range(0,len(blocks),2)]
        self.proofs.append(Case(f"no_max_tau_{self.r}",f"∀ n, Small n {self.r} → ¬ {self.r}∣n.divisors.card",
                              [f"  intro n H hd",f"  exact impossible_of_roots (M:={M}) (by norm_num) "
                               f"{decide} {blocks[0]} H hd"]))

    def write(self, directory, chunk):
        directory.mkdir(parents=True,exist_ok=True)
        ns=f"OddPerfect.HarmonicTau{self.r}"
        def emit(name,dep,lines):
            s=["module","",f"public import {dep}","import Mathlib.Tactic.Primality","",
               "public section","","namespace OddPerfect.HarmonicChain","","open FactorBudget","",
               "set_option maxRecDepth 16000","",*lines,"end OddPerfect.HarmonicChain",""]
            (directory/f"{name}.lean").write_text("\n".join(s))
        previous="OddPerfect.HarmonicRoots"
        ordered=sorted(self.primes)
        for off in range(0,len(ordered),32):
            lines=[]
            for p in ordered[off:off+32]:
                lines.extend([f"theorem htauPrime{self.r}_{p} : Nat.Prime {p} :=",
                              "  "+factorer.prime_proof(p),""])
            name=f"Primes{1+off//32:02d}"
            emit(name,previous,lines)
            previous=ns+"."+name
        for off in range(0,len(self.proofs),chunk):
            lines=[]
            for case in self.proofs[off:off+chunk]:
                lines.extend([f"theorem {case.name} : {case.head} := by",*case.body,""])
            name=f"Part{1+off//chunk:03d}"
            emit(name,previous,lines)
            previous=ns+"."+name
        print(self.r,dict(self.counts),len(self.primes),"prime witnesses",previous,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prime",type=int,choices=[5,7,11,13,17,19,23,29,31])
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--chunk",type=int,default=30)
    args=parser.parse_args()
    chain=Chain(args.prime)
    chain.generate()
    chain.write(args.output,args.chunk)
