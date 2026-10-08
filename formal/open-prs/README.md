# Lean check of the open pull requests #3–#12

Scope: the upstream pull requests #1–#12 open on 2026-10-08, at the head commits listed
in `data/MANIFEST.json`. Later pull requests (#13 onward) are not covered.

- #1 and #2 are based on the older 2^-59 release and are superseded by κ = 83/10¹².
  They were audited but not Lean-checked.
- #11 makes no new κ claim; its negative screens are checked.

For every other PR, the certificate arithmetic is proved in Lean:

- the network counts and η;
- the logarithm bounds and the exponent certificates (or the weighted moments);
- every constraint slack and margin;
- min margin > κ, and the stated dyadic comparisons.

| PR | headline κ | Lean library |
|---|---|---|
| #3 | 59/10¹¹ | `PRChecksA.PR3` |
| #4 | 591/10¹² | `PRChecksA.PR4` |
| #5 | 1479/10¹² | `PRChecksB.PR5` (with its h = 50 paired bit network), plus `PRChecksB.PR5Analytic` for its analytic inequalities |
| #6 | 1624/10¹² | `PRChecksB.PR6` |
| #7 | 373/10¹¹ | `PRChecksB.PR7` |
| #8 | 59/10¹¹ | `PRChecksA.PR8` |
| #9 | 19/(5·10⁹) | `PRChecksC.PR9` |
| #10 | 6149999/(5·10¹³) | `PRChecksC.PR10`, including the bulk-guard Taylor bound |
| #11 | none | `PRChecksC.PR11` |
| #12 | 12649/10¹¹ | `PRChecksC.PR12` |

**Taken as given:** circuit outputs such as role counts, which are stated as
definitions. Constructions written only in prose are not checked. OpenAI's theorem and
the Harvey–van der Hoeven results are assumed.

## Running

```
cd formal/lean && lake build                       # all four libraries
python3 formal/open-prs/drift_A.py                 # #3, #4, #8
python3 formal/open-prs/drift_B.py --selftest      # #5, #6, #7
python3 formal/open-prs/drift_C.py                 # #9-#12
python3 formal/open-prs/axioms/check_axioms_B.py   # #print axioms, PRChecksB
(cd formal/lean && lake env lean ../open-prs/axioms/AxiomsC.lean)
```

`PRChecksA` prints its axioms during the build.

What the drift tests check (a literal "occurs" as a whole token, outside comments):

- `drift_A.py`: each certificate value and quoted note line against a literal in every named
  declaration; every certificate leaf and every Lean literal of four or more digits is
  accounted for.
- `drift_B.py`: the literal on each line tagged `-- json …`; a tag on every core certificate
  value and numeric definition; the exponent certificates and deficit slacks use their
  tagged savings (`USES`); the `PR5Analytic` constants against the vendored note and script
  lines (`LINES`).
- `drift_C.py`: its certificate rows, the assembly entry by entry, and every Lean literal of
  four or more digits.

Not every literal is checked: proof steps and short literals outside the rows are not. The
certified savings and θ̄ are also tied in Lean (`exponents_certified`, `path_moments` via
`path_moment_rational`). `tests/test_open_pr_lean.py` applies eleven weakening mutations and
requires each to fail its drift test.

The PR files are vendored in `data/`. `data/MANIFEST.json` records each file's PR head
commit and SHA-256, and the test fails if a vendored file changes. All 334 theorems use only
`propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or `native_decide`.

## Findings

No certificate value is wrong. The claims that need fixing:

1. **#3 and #8: the "next ceiling" is not a ceiling for the published network.**
   κ < 5.92·10⁻¹⁰ holds only with the bit exponent fixed at 1 − 296/10¹¹. The published
   h = 50 network certifies 1 − τ = 2964/10¹² (`PRChecksA.tau_2964_certified`). With it,
   κ = 5923/10¹³ meets every constraint (`beyond_fixed_tau_ceiling_3`, `_8`). The
   ceiling for that network is κ < 593/10¹² (`ceiling_any_certified_tau`), so κ < 2⁻³⁰
   still holds.
2. **#3:** `docs/research/complex-circuit.md:102` writes `a_b/5 < 5.92e-10`. Since
   a_b/5 = 5.92·10⁻¹⁰ exactly, it should be `=` (`docs_line_102_is_equality`).
3. **#4: the notes describe an older construction.** They give R_aux = 365760 and
   1 − σ = 750/10¹¹; the certificate has R = 90950 and 1 − σ = 2970/10¹¹. The older
   numbers are internally consistent (`rect_*`). The notes are invalid as written; the
   certificate and κ check.
4. **#5 and #6: κ < a/2 is a ceiling only with τ fixed, as in finding 1.** The published
   networks certify more: 1 − τ = 29643/10¹³ (paired, #5) and 325018/10¹⁴ (aligned, #6).
   With these, κ = 14820/10¹³ (#5) and 162508/10¹⁴ (#6) meet all 29 slacks and seven
   margins (`Certified.fixed_tau_ceiling_beaten`). The ceilings for these networks are
   κ < 14825/10¹³ and κ < 16254/10¹³ (`Certified.certified_ceiling`), within 5/10¹³ and
   32/10¹⁴ of the attained values, so κ < 2⁻²⁹ still holds. Also, "g₂, g₃, g₄ ≤
   a·min{ε, 1 − ε}" is false for g₄; what is true is min{g₃, g₄} ≤ a·min{ε, 1 − ε}
   (`min_g3_g4_le`, `g4_exceeds_a_min`).
5. **#6:** "a further 3% on a_b would close this window" holds only at β = 19/25. The
   window closes at about 7.7% (`window_size`).
6. **#5: wording around the Harvey–van der Hoeven lemmas.** The proofs still hold, but:
   - the text should say θ ≥ p/α⁴ was also used to obtain α²θ ≥ 1;
   - it should add that the proofs of Lemmas 4.8, 4.9 and 4.11 use only 2 ≤ α < √p,
     s < t < 2^p, p ≥ 100 and the norms of Proposition 4.7(i);
   - in the E map, F = e^(πα²/4) fails once α ≥ 21. Use F := 2^⌈1.14α²⌉; P = 34p still
     suffices.
