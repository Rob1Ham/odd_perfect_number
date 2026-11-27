# Palomar proof references for the Descartes theorems

Each export is a standalone Lake project with its Lean toolchain, dependency
manifest, and the transitive local proof sources for one theorem. It contains
one statement that a reviewer can read using only Mathlib, a separate proof
module, and the Comparator configuration for that declaration.
The export deliberately gives the Challenge a proof hole. The Solution imports
the project proof. Comparator checks the two modules independently. Both
statements expand the Descartes predicates, so there are no project-specific
definitions for the reviewer to trust.

From the `odd_perfect_number` root, generate either packet in a **new**
directory. The script uses only the Python standard library.

```sh
python3 submissions/formal-conjectures/palomar/prepare.py toth /tmp/descartes-toth
python3 submissions/formal-conjectures/palomar/prepare.py cube-free /tmp/descartes-cube-free
```

| Packet | Result selected by Comparator | Provenance for the metadata |
| --- | --- | --- |
| `toth` | For a Descartes factorization other than the historical example, the cofactor exceeds one trillion. The solution imports `OddPerfect.TothTrillion`. | L. Tóth, “On the Density of Spoof Odd Perfect Numbers” (2021), Theorem 1. [Paper](https://doi.org/10.12921/cmst.2021.0000005) · [Public Lean proof](https://github.com/Rob1Ham/odd_perfect_number/blob/841bbce6a93f3b79aac04bb79f845a878057d124/OddPerfect/TothTrillion.lean#L23-L29) |
| `cube-free` | A cube-free Descartes integer with fewer than seven distinct prime divisors equals 198585576189. The solution imports `CubeFree` and calls `DescartesSubmission.catalog_cubeFree_lt_seven_primeFactors_unique`. | W. D. Banks, A. M. Güloğlu, C. W. Nevans and F. Saidak, “Descartes numbers” (2008). [Paper](https://doi.org/10.1090/crmp/046/12) |

Both exported projects passed their default `lake build` on Lean 4.36.0 with
cached dependencies. Axiom reports for both exported Solution declarations
listed exactly `propext`, `Classical.choice` and `Quot.sound`. Tóth's export
contains 62 proof modules and the cube-free export contains 78. The
sandboxed `lake comparator` command stops
before verification on this macOS machine because Bubblewrap requires Linux
namespaces. Registry verification and registration are pending.

## Assembling a registerable snapshot

1. From a newly exported directory run `lake exe cache get` to fetch
   Mathlib's compiled dependencies, then `lake build`. The default targets
   are `Challenge` and `Solution`. The intentional warning comes from the
   Challenge. The cube-free project includes `CubeFree.lean` and all four
   companion modules under their buildable module names. Keep the exact
   toolchain and manifest with the sources when preparing a public snapshot.
2. Add the rights holder's choice of an accepted SPDX licence, with its
   full text in exactly one conventional root licence file. The source project
   has no root licence at the linked Tóth commit. Each dedicated export omits
   unrelated source and audit files. If adding files to the public snapshot,
   check that every Lean source uses `module` and is at most 10,000 lines;
   Palomar also checks unused source.
3. Complete the exported `formalization.yaml.in` and save it as
   `formalization.yaml`. It supplies the result, literature reference,
   classification and Lean declaration. Supply the confirmed human
   formalization authors and responsible maintainers, the matching SPDX
   identifier, and the actual relationship to the published proof.
   Use `independently-proves` for an independent proof or `formalizes` for a
   formalization of the cited argument. Classify as `math.NT` (MSC `11A25`
   applies), list material AI assistance under `automation.methods`, and
   report the review that actually took place. These are previously published
   mathematical results. If submitting a separate thin wrapper, fill
   `repository.substantive_formalization` with the actual public repository
   and full revision. [Metadata template](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/formalization.yaml)
4. On a Linux system with Bubblewrap and NanoDa available, run
   `lake comparator --config comparator.json` from the exported project.
   The required proof axiom allowance is limited to `propext`, `Quot.sound`
   and `Classical.choice`. Palomar independently rechecks with NanoDa.
   Local Lean compilation and an axiom report are useful checks before this
   step. [Comparator](https://github.com/leanprover/comparator#comparator)
5. Submit the exact public repository, full 40-character commit SHA and
   repository-relative Comparator configuration path to Palomar. The
   substantive project's responsible maintainer or their approved submitter
   supplies the authorization. Review the returned report before choosing to
   register. Use its actual registered entry URL in DeepMind's
   `formal_proof using lean4 at` annotation. Each packet has its own
   configuration and can receive its own entry. [Palomar submission guide](https://palomar-registry.org/how-to-submit) · [Binding submission requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

The Tóth [companion DeepMind patch](../toth/formal-conjectures.patch) uses
their documented exception for an existing public proof. The cube-free packet
requires a public snapshot containing its completed proof before registration.
