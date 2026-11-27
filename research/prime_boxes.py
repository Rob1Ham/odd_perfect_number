"""Produce formal exclusion trees for the ordered, genuine prime-power slots."""

import argparse
from dataclasses import dataclass, replace
from fractions import Fraction
from functools import cache
from math import isqrt
from pathlib import Path
import re

from count_chain import Factorer

from spoof_boxes import Slot, abundancy, branches, last_solution
from spoof_certificate import lean_rows


@cache
def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


small_primes = [p for p in range(3,10000,2) if is_prime(p)]


@cache
def demands(b, length):
    value = (b**length - 1)//(b-1)
    while value % 2 == 0:
        value //= 2
    result = []
    for p in small_primes:
        if p*p > value:
            break
        if value % p == 0:
            result.append(p)
            while value % p == 0:
                value //= p
    if 1 < value < 10**8 and is_prime(value):
        result.append(value)
    return result


@cache
def next_base(lo, stride, banned):
    p = lo + (1-lo) % stride
    while p == banned or not is_prime(p):
        p += stride
    return p


@cache
def previous_base(hi, stride, banned):
    p = hi - (hi-1) % stride
    while p >= 3 and (p == banned or not is_prime(p)):
        p -= stride
    return max(p,1)


@dataclass
class Proof:
    name: str
    start: list
    operations: list
    terminal: str


def search(k, special):
    proofs = []
    prefix = f"rank{k}_{special}_"
    def visit(start):
        rows = start.copy()
        ops = []
        def finish(terminal):
            name = prefix+str(len(proofs))
            proofs.append(Proof(name,start,ops,terminal))
            return name
        def update(j, slot, operation):
            rows[j] = slot
            ops.append((operation,rows.copy()))
        for _ in range(2*k+4):
            old = rows.copy()
            fixed = {s.base_lo for s in rows if s.base_hi == s.base_lo}
            if {3,5,7}.issubset(fixed):
                return finish("exact covered_impossible_prime_rows _ (by decide +kernel)")
            banned = 7 if 5 in fixed else 5 if 7 in fixed else 0
            for j,s in enumerate(rows):
                start_lo = max(s.base_lo,rows[j-1].base_lo+1) if j else s.base_lo
                lo = next_base(start_lo,s.stride,banned)
                if lo != s.base_lo:
                    update(j,replace(s,base_lo=lo),f"apply covered_prime_lower _ {j} {lo} {start_lo} {banned} "
                           "(by decide +kernel) (by decide +kernel) (by decide +kernel)")
                if s.base_hi and s.base_hi < lo:
                    return finish("exact primeCovered_reject _ (by decide +kernel)")
            for j in reversed(range(k)):
                s = rows[j]
                after = rows[j+1].base_hi if j+1<k else 0
                stop = min(s.base_hi or after-1,after-1) if after else s.base_hi
                if stop:
                    hi = previous_base(stop,s.stride,banned)
                    if hi != s.base_hi:
                        update(j,replace(s,base_hi=hi),f"apply covered_prime_upper _ {j} {hi} {stop} {banned} "
                               "(by decide +kernel) (by decide +kernel) (by decide +kernel)")
                    if hi < s.base_lo:
                        return finish("exact primeCovered_reject _ (by decide +kernel)")
            required = {}
            for i,s in enumerate(rows):
                if s.base_lo == s.base_hi and (s.exp_lo == s.exp_hi or s.special):
                    length = s.exp_lo+1 if s.exp_lo == s.exp_hi else 2
                    for r in demands(s.base_lo,length):
                        required.setdefault(r,i)
            for r,src in required.items():
                options = [i for i,s in enumerate(rows) if s.base_lo<=r and
                           (not s.base_hi or r<=s.base_hi) and r % s.stride == 1]
                if not options:
                    return finish(f"exact primeCovered_missing _ {src} {r} (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)")
                if len(options) == 1:
                    j = options[0]
                    s = rows[j]
                    if s.base_lo != r or s.base_hi != r:
                        update(j,replace(s,base_lo=r,base_hi=r),f"apply covered_force_base _ {src} {j} {r} "
                               "(by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)")
            if rows == old:
                break

        low = high = Fraction(1)
        choices = []
        free = []
        for j,s in enumerate(rows):
            l = abundancy(s.base_hi,s.exp_lo)
            u = abundancy(s.base_lo,s.exp_hi)
            mid = abundancy(s.base_lo,s.exp_lo)
            low *= l
            high *= u
            if s.base_lo != s.base_hi or s.exp_lo != s.exp_hi:
                free.append(j)
            if s.base_lo != s.base_hi:
                choices.append(((mid-l)/l*(4 if s.exp_lo==s.exp_hi else 1), j, False))
            if s.exp_lo != s.exp_hi:
                choices.append(((u-mid)/u*(16 if s.base_lo==s.base_hi else 1), j, True))
        if (low>2 or high<2 or (low==2 and any(not s.base_hi for s in rows))
                or (high==2 and any(not s.exp_hi for s in rows))):
            return finish("exact primeCovered_reject _ (by decide +kernel)")
        if len(free) == 1:
            i = free[0]
            solution = last_solution(rows,i)
            if solution and all(is_prime(b) for b,e in solution):
                raise ValueError(f"genuine candidate: {solution}")
            return finish(f"exact primeCovered_last _ {i} (by decide +kernel)")
        if not choices:
            raise ValueError(f"unclosed point: {rows}")
        _,i,exponent = max(choices)
        left,right = branches(rows,i,exponent)
        cut = rows[i].exp_lo if exponent else rows[i].base_cut()
        lc = visit(left)
        rc = visit(right)
        axis = "exponent" if exponent else "base"
        return finish(f"exact primeCovered_split _ {i} .{axis} {cut} {lc} {rc}")
    rows = [Slot(i==special,5 if i==special else 3,0,1 if i==special else 2,0) for i in range(k)]
    rows[0] = replace(rows[0],base_hi=3)
    rows[-1] = replace(rows[-1],base_lo=max(rows[-1].base_lo,258))
    root = visit(rows)
    return proofs, root


def write_rank(k,special,chunk,directory,prime_cutoff):
    directory.mkdir(parents=True,exist_ok=True)
    proofs,root = search(k,special)
    witnesses = set()
    def with_witnesses(line):
        def substitute(match):
            p = int(match.group(1))
            if p < prime_cutoff:
                return match.group()
            witnesses.add(p)
            return f" {p} rank{k}_{special}_prime{p}"
        return re.sub(r" (\d+) \(by norm_num\)", substitute, line)
    previous = "OddPerfect.PrimeCover"
    for offset in range(0,len(proofs),chunk):
        lines=["module", "", f"public import {previous}", "import Mathlib.Tactic.NormNum.Prime", "", "public section", "", "set_option maxRecDepth 16000", "", "namespace OddPerfect.SpoofBox", ""]
        for proof in proofs[offset:offset+chunk]:
            lines.append(f"theorem {proof.name} : PrimeCovered ({lean_rows(proof.start)} : Vector Slot {k}) := by")
            for op,after in proof.operations:
                lines.extend(["  "+op,f"  change PrimeCovered ({lean_rows(after)} : Vector Slot {k})"])
            lines.extend(["  "+proof.terminal,""])
        last = offset+chunk >= len(proofs)
        if last:
            lines.extend([f"theorem closed_prime_{k}_{special} : PrimeCovered (primeInitial ({special} : Fin {k})) := {root}", ""])
        lines.extend(["end OddPerfect.SpoofBox",""])
        part=f"Part{1+offset//chunk:03d}"
        lines = [with_witnesses(line) for line in lines]
        if any(f"rank{k}_{special}_prime" in line for line in lines):
            lines.insert(3, f"import OddPerfect.PrimeRank{k}_{special}.Witnesses")
        (directory/f"{part}.lean").write_text("\n".join(lines))
        previous=f"OddPerfect.PrimeRank{k}_{special}.{part}"
    if witnesses:
        factorer=Factorer(10)
        lines=["module", "", "public import Mathlib.Data.Nat.Prime.Defs", "import Mathlib.Tactic.Primality", "", "public section", "",
               "namespace OddPerfect.SpoofBox", ""]
        for p in sorted(witnesses):
            lines.extend([f"theorem rank{k}_{special}_prime{p} : Nat.Prime {p} :=", "  "+factorer.prime_proof(p), ""])
        lines.extend(["end OddPerfect.SpoofBox",""])
        (directory/"Witnesses.lean").write_text("\n".join(lines))
    print("rank",special,"nodes",len(proofs),"operations",sum(len(z.operations) for z in proofs),"import",previous,flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k",type=int)
    parser.add_argument("rank",type=int)
    parser.add_argument("--chunk",type=int,default=24)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--prime-cutoff",type=int,default=1024)
    args=parser.parse_args()
    write_rank(args.k,args.rank,args.chunk,args.output,args.prime_cutoff)
