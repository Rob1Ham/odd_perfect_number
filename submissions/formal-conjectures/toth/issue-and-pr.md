# Tóth’s cofactor bound

Private contributor notes. Write the public issue in your own words, and explain the role of AI in the PR description. [DeepMind contribution guidelines](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md) · [Mathlib AI conventions](https://leanprover-community.github.io/contribute/index.html#use-of-ai)

## Proposed issue

**Title** Add a Lean proof reference for Tóth’s Descartes cofactor bound

The declaration `DescartesNumber.descartes_non_example_factor_gt_ten_pow_twelve` already records Tóth’s theorem as research solved. An existing public Lean 4 formalization proves that the cofactor $m$ exceeds $10^{12}$ for every factorization $mw$ different from Descartes’s example. Would maintainers accept a declaration-local link to the existing formalization, or prefer a Palomar entry first?

[Catalog statement](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/DescartesNumber.lean#L149-L155) · [External proof](https://github.com/Rob1Ham/odd_perfect_number/blob/841bbce6a93f3b79aac04bb79f845a878057d124/OddPerfect/TothTrillion.lean#L23-L29)

## Proposed pull request

**Title** Link the Lean formalization of Tóth’s cofactor bound

Add a `formal_proof using lean4` reference to the existing research-solved statement. The linked theorem is `OddPerfect.trillion_lt_spoof_cofactor`. Oddness of $mw$ gives oddness of both factors. Upstream’s composite predicate supplies $1<w$ and nonprimality of $w$. Coprimality and the divisor-sum equation supply the remaining hypotheses after reassociating multiplication. Both statements exclude $mw=198585576189$ and conclude $10^{12}<m$.

The linked commit contains the external proof and its finite certificate. The patch uses the documented existing-proof exception for this declaration. If maintainers prefer the registry route, substitute the published Palomar entry for the link and omit the linter option.

Before sending, add the real issue number, the actual downstream and upstream build results, and a truthful AI-assistance disclosure matching the submitter’s review. Google requires a CLA from the contributor or their employer.
