# MathOverflow 310919 — which residue is impossible?

[Question](https://mathoverflow.net/q/310919) · [Dris’s existing answer](https://mathoverflow.net/a/340106) · [Chen and Luo, *Odd multiperfect numbers*, Theorem 3.3, equations (5) and (6)](https://doi.org/10.1017/S0004972712000858) · [Lean proof, pinned source](https://github.com/Rob1Ham/odd_perfect_number/blob/841bbce6a93f3b79aac04bb79f845a878057d124/OddPerfect/ChenLuo.lean#L57-L94)

Write the hypothetical odd perfect number in Euler form as $q^a m^2$, with $q$ the special prime. Both $q$ and $a$ are 1 modulo 4. These are the four possibilities in the question.

| $q\bmod 8$ | $a\bmod 8$ | Forced $\sigma(m^2)\bmod 4$ | Impossible $\sigma(m^2)\bmod 4$ |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 3 |
| 1 | 5 | 3 | 1 |
| 5 | 1 | 3 | 1 |
| 5 | 5 | 1 | 3 |

Chen and Luo prove that $\sigma(m^2)\equiv1\pmod4$ is equivalent to $q\equiv a\pmod8$, and that $\sigma(m^2)\equiv3\pmod4$ is equivalent to $q\equiv a+4\pmod8$. Their theorem applies to odd perfect numbers by taking the multiplier to be two. The impossible value is the complementary odd residue in each row.

The mathematical answer is already in Dris’s post. The addition from this project is a reproducible formalization. `OddPerfect.chen_luo_congruences` gives the two equivalences and `OddPerfect.sigma_square_mod_eight_of_euler` gives the intermediate congruence

$$\sigma(m^2)\equiv q\left(\frac{q+1}{2}\right)\left(\frac{a+1}{2}\right)\pmod 8.$$

In particular, the two residues $q,a\bmod 16$ determine $\sigma(m^2)\bmod 8$. Run `lake env lean submissions/formal-conjectures/mathoverflow-310919/Check.lean` in the proof repository to inspect their types and axioms.

## Contributing to the discussion

A brief comment on the existing answer linking the pinned Lean proof would add the new information without duplicating the answer. These are private reference notes for your own independently authored contribution. MathOverflow requires contributors to author the mathematical content themselves. Its [generative AI policy](https://mathoverflow.net/help/gen-ai-policy) describes permissible language assistance and attribution.
