# Four prime powers and a formal fifth component

Write $G(b,e)=1+b+\cdots+b^e$. The certificate tests whether

$$
\left(\prod_{i=1}^4 G(p_i,e_i)\right)G(x,a)
  =2\left(\prod_{i=1}^4 p_i^{e_i}\right)x^a.
$$

The $p_i$ are four increasing odd primes and the $e_i$ are positive even integers. The fifth base $x>1$ and its exponent $a>0$ are both one modulo four. The fifth base can be composite, can lie between any of the four primes, and can share factors with them. Only the first four entries have to be prime. [Slot hypotheses and representation](../OddPerfect/DeficientSlots.lean)

## Linear fifth component and the Yang–Togbé theorem

For an odd deficient-perfect number $n$ with deficient divisor $d$, put $x=2n/d-1$. Then $n$ is a square, $x\equiv1\pmod4$, and $\sigma(n)(x+1)=2nx$. With four distinct prime divisors, the least prime is 3 and the second prime is one of $5,7,11,13,17$. These reductions give five starting rectangles with $a=1$. The exponents of all four primes, the two largest primes, and $x$ have no upper bounds. [Realization of the five cases](../OddPerfect/DeficientSlots.lean) · [Bound on the second prime](../OddPerfect/DeficientLargeSecond.lean)

| Second prime | Search nodes | Certified subtrees | Root declaration |
|---:|---:|---:|---|
| 5 | 2,577 | 71 | `closedSecond5` |
| 7 | 383 | 11 | `closedSecond7` |
| 11 | 341 | 9 | `closedSecond11` |
| 13 | 135 | 4 | `closedSecond13` |
| 17 | 77 | 1 | `closedSecond17` |

The unique balanced tuple identified by the 3,513 nodes is $(3,2),(7,2),(11,2),(13,2),(22021,1)$. It gives $n=3^2 7^2 11^2 13^2=9{,}018{,}009$ and $d=n/11011=819$. The condition $\sigma(n)+d=2n$ determines $d$ uniquely. This is the conclusion of Yang and Togbé’s Theorem 1. The interval proof covers their complete four-prime problem, including the unbounded exponents in §5.3. [Yang and Togbé, *Integers* 23 (2023), A5](https://math.colgate.edu/~integers/x5/x5.pdf) · [Recovery and verification of the deficient divisor](../OddPerfect/DeficientSlots.lean)

## Fifth exponent at least five

The second certificate begins with a single rectangle. All four primes range from 3 to infinity, all four even exponents range from 2 to infinity, and the fifth base and exponent range from 5 to infinity in the residue class one modulo four. The search has 4,717 nodes and 6,461 individual narrowing steps. Its 2,358 branch nodes split a base 744 times, an ordinary exponent 1,479 times and the fifth exponent 135 times. Of the 2,359 leaves, 753 fail an interval test and 1,606 lack a recipient for a required prime divisor. There are no balanced tuples. The 131 subtree declarations form 27 modules. The final declaration is `OddPerfect.DeficientSlots.closedPowerGeneral`. [Unrestricted root](../OddPerfect/DeficientPowerReplayGeneral/Part027.lean)

This extension concerns the formal five-component equation. Yang and Togbé’s deficient-perfect condition gives $a=1$. For an odd perfect number with exactly five distinct prime factors, Euler’s form gives four square components and a genuine prime fifth base. Every Euler exponent above one lies in the higher-exponent rectangle. At exponent one, the classification of the cofactor would require the composite base $22021=19^2\cdot61$. Together with the lower bound of five prime divisors this yields the classical bound of six. Sylvester announced this bound in 1888. Gradshtein published a proof in 1925. [Euler form](../OddPerfect/Euler.lean) · [Five-prime lower bound](../OddPerfect/FewPrimes.lean) · [Sylvester’s announcement](https://rcin.org.pl/impan/Content/122671/PDF/WA35_145312_11371-4_Art55.pdf) · [Gradshtein, *Matematicheskii Sbornik* 32 (1925), 476–510](https://www.mathnet.ru/eng/sm7412)

## Checking the certificates

An odd prime $r$ dividing a component sum must equal one of the four genuine primes or divide $x$. For fixed $x$, the factor $x+1$ supplies divisors at every admissible fifth exponent. The state records a known divisor $g\mid x$, starting with $g=1$. When only the fifth base can receive $r$, the next state uses $\operatorname{lcm}(g,r)$. When only one genuine prime can receive $r$, that prime is fixed to $r$. If neither possibility remains, the branch closes. The first multiple of $g$ in the class one modulo four decides whether any multiplier is available within bounded endpoints. The search uses divisibility witnesses up to 1,999. Its largest selected witness is 1,871. These numbers bound the search for a witness, while the theorem quantifies over arbitrary bases and exponents. [Divisibility and transition proofs](../OddPerfect/DeficientTree.lean) · [Multiplier, prime intervals, and exponent splits](../OddPerfect/DeficientCuts.lean)

The ordinary interval test compares products of lower and upper bounds for $G(b,e)/b^e$ with 2. It uses the limiting values 1 for an unbounded base and $b/(b-1)$ for an unbounded exponent, and accounts for strictness at these endpoints. Each arithmetic tightening carries a separate rejection for the discarded interval. The two one-free-component leaves in the linear search recover the last base and exponent exactly. Each subtree reference in the generated source supplies its initial rows and multiplier divisor, and the checker compares both with the state at the point of use. [Interval tests](../OddPerfect/SpoofBoxes.lean) · [Single remaining component](../OddPerfect/SpoofLast.lean) · [Checker and soundness theorem](../OddPerfect/DeficientTree.lean)

From the repository root, the following commands regenerate the Lean modules and run the generator’s independent arithmetic replay. All bounds use integers or rational arithmetic. Each Lean subtree applies `Tree.sound` to a Boolean decision made by the kernel. [Generator](deficient_four_search.py)

```sh
python3 research/deficient_four_search.py --lean OddPerfect
python3 research/deficient_four_search.py --higher --unrestricted --lean OddPerfect
lake build OddPerfect.DeficientReplay5.Part015 OddPerfect.DeficientReplay7.Part003 OddPerfect.DeficientReplay11.Part002 OddPerfect.DeficientReplay13.Part001 OddPerfect.DeficientReplay17.Part001
lake build OddPerfect.DeficientPowerReplayGeneral.Part027
```

The optional `--json PATH` writes the operation stream in postorder. The SHA-256 digests with the default witness limit are `b3719f87bc3564b0ec7af62afe8311ae7338dbfe6054433126a384be099094e8` for the five linear roots and `660564671e9d4ed264540ff87f8401998f36d380f53c77b4b39325e56ccee7ad` for the unrestricted higher-exponent root.
