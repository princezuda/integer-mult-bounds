import PRChecksB.PR5

/-!
# PR #6 (aligned bit circuit with cheaper centers, κ = 1624/10¹²): certificate arithmetic

Source: `certificates/aligned-bit-network.json`, written by
`scripts/aligned_bit_network.py`, in worktree `/home/user/prs/pr6` (head `5015011`, on
top of PR #5 `d3d370c`); notes `notes/aligned-bit-note.tex`,
`notes/aligned-bit-construction.tex`, `docs/research/aligned-bit.md`.

* **A.** aligned bit network at `h = 50`, *given* the circuit's `435346` additions,
  `58800` partial outputs (both produced by running `AlignedPairedCircuit(50)`; taken as
  given) and `h = 50` center roles, so `R = 494196`: counts with
  `W = 2N + 2v²R`, `L = 3v²h(h-1)`, `D = N - 2L`, `s = W m - D`,
  `η_b = 49/1284490000`, `log 125000 < 11737/1000`, and `s/W < 125000^τ` with
  `1 - τ = 325/10¹¹`.
* **B.** the witness: guard (unchanged complex network, `β = 19/25`), 29 fast-Gaussian
  slacks, margins, `min g = g3 = 162446751/10¹⁷`, `2^-30 < κ < 2^-29`, the leaf and guard
  windows, and the scoped ceiling `κ < a/2 = 13/8000000000` **for τ fixed at `1 - a`**.
* **C.** the ceiling for the published aligned network: it certifies `1 - τ = 325018/10¹⁴`,
  so `a/2` is not a ceiling; every certified `τ` gives `κ < 16254/10¹³ < 2^-29`, and
  `κ = 162508/10¹⁴` is attained.
-/

namespace PRChecksB.PR6

open Real

/-! ## A. The aligned bit network -/

/-- additions of `AlignedPairedCircuit(50)` (including the 50 group totals):
**taken as given** (produced by running the circuit) -/
def cAdd : ℕ := 435346  -- json aligned-bit-network.json circuit.additions
/-- partial outputs: **taken as given** (equals `50·C(49,2) = 3v`, checked below) -/
def q : ℕ := 58800  -- json aligned-bit-network.json circuit.side_outputs
/-- roles per invocation `R = c + q + h`, including the center wires -/
def R : ℕ := 494196  -- json aligned-bit-network.json bit_counts.side_and_center_roles

/-- the certified bit saving `a = 325/10¹¹` -/
def aB : ℚ := 13 / 4000000000  -- json aligned-bit-network.json bit_saving

def v : ℕ := Nat.choose 50 3
def m : ℕ := 50 ^ 3  -- json aligned-bit-network.json bit_counts.m
def N : ℕ := v ^ 3
/-- `W = 2N + 2v²R` (`counts_from`) -/
def W : ℕ := 2 * N + 2 * v ^ 2 * R
/-- `L = 3v²h(h-1)`: each center wire loses `h - 1` -/
def L : ℕ := 3 * v ^ 2 * 50 * 49
def D : ℕ := N - 2 * L
def s : ℕ := W * m - D

theorem v_eq : v = 19600 := by decide
theorem c49 : Nat.choose 49 2 = 1176 := by decide

theorem roles :
    R = cAdd + q + 50 ∧ q = 50 * Nat.choose 49 2 ∧ q = 3 * v ∧
    -- the published paired network's roles plus its 50 center wires
    PR5.R50 + PR5.hb = 509244  -- json aligned-bit-network.json bit_counts.published_roles
    := by
  simp only [R, cAdd, q, v_eq, c49, PR5.R50, PR5.hb]; norm_num

theorem counts :
    v = 19600 ∧  -- json aligned-bit-network.json bit_counts.v
    m = 125000 ∧  -- json aligned-bit-network.json bit_counts.m
    N = 7529536000000 ∧  -- json aligned-bit-network.json bit_counts.N
    W = 394759742720000 ∧  -- json aligned-bit-network.json bit_counts.W
    L = 2823576000000 ∧  -- json aligned-bit-network.json bit_counts.L
    D = 1882384000000 ∧  -- json aligned-bit-network.json bit_counts.deficit
    s = 49344965957616000000 ∧  -- json aligned-bit-network.json bit_counts.s
    2 * L < N ∧ D ≤ W * m ∧
    -- the note's form `s = W m - N + 6v²h(h-1)` (Proposition `aligned-bit-interface`)
    s = W * m + 6 * v ^ 2 * 50 * 49 - N ∧
    -- the previous paired network's deficit `N - 6v²h²`
    N - 6 * v ^ 2 * 50 ^ 2 = 1767136000000  -- json aligned-bit-network.json previous_counts.deficit
    := by
  simp only [W, L, D, s, N, m, R, v_eq]; norm_num

theorem eta :
    ((D : ℕ) : ℚ) / (W * m) = 49 / 1284490000  -- json aligned-bit-network.json bit_counts.eta
    := by
  simp only [W, L, D, N, m, R, v_eq]; norm_num

/-- `docs/research/aligned-bit.md`: `η_b = (v - 6·loss)/(2m(v+R))`, numerators
`v - 6h(h-1) = 4900` (new) and `v - 6h² = 4600` (old), the old deficit `23/661055000` -/
theorem eta_numerators :
    ((19600 - 6 * 50 * 49 : ℚ)) / (2 * 125000 * (19600 + 494196)) = 49 / 1284490000 ∧
    (19600 : ℤ) - 6 * 50 * 49 = 4900 ∧ (19600 : ℤ) - 6 * 50 ^ 2 = 4600 ∧
    ((19600 - 6 * 50 ^ 2 : ℚ)) / (2 * 125000 * (19600 + 509244)) = 23 / 661055000 := by
  norm_num

theorem deficit_slack :
    (49 / 1284490000 : ℚ) - aB * (11737 / 1000) =
      1123131 / 513796000000000000  -- json aligned-bit-network.json bit_deficit_slack
    := by norm_num [aB]

theorem log_m : Real.log 125000 < 11737 / 1000  -- json aligned-bit-network.json log_m_upper
    := log_125000

/-- the certificate's rational log enclosure (`log_integer_bounds`) -/
def encLo : ℚ :=
  6099021614163970750340690270747048593377313595259644611596156469001853135272242759283756451534639148254765636471177483214300622977245445698096345111777677170484861520093166271979500958689459600180523495577246701335944207232 / 519681812172478230053097754325168673714744405889689912096132382607554732184741571090356759292354384059377809602698438669332095130139331867848781351965500521204384477208981402624951508924926641274448754509753308495941664525  -- json aligned-bit-network.json log_enclosure.0
def encHi : ℚ :=
  145725956434424474461473597751120889802694653985144545340380983586320956935675283688048364336111969626569994401607304138478915484537765084900200459272334204754568463440328943564474156248014219334148004222790801045949275508263504721 / 12416930765507746510068682343342696843957626338057657633016923061769841067667425271918924168691987416458733797440474694605908192976129102762466882436295692453310093108779928980052174719912913882184162241086372384329699504384000000  -- json aligned-bit-network.json log_enclosure.1

/-- the enclosure contains `log 125000 = 117A + 87B + 51C` (`A = -log(15/16)`, …, series to
`10⁻²⁷`), and its upper end is below the stated bound -/
theorem log_enclosure_hi_lt :
    (encLo : ℝ) < Real.log 125000 ∧ Real.log 125000 < encHi ∧ encHi < 11737 / 1000 := by
  have h := log_prod 117 87 51 125000 (by norm_num)
  have a := neglog_bounds (1 / 16) (by norm_num) (by norm_num) 24
  have b := neglog_bounds (1 / 25) (by norm_num) (by norm_num) 21
  have c := neglog_bounds (1 / 81) (by norm_num) (by norm_num) 15
  unfold ps at a b c
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at a b c
  norm_num at a b c h
  rw [h]
  refine ⟨?_, ?_, by norm_num [encHi]⟩
  · unfold encLo; push_cast; linarith [a.1, b.1, c.1]
  · unfold encHi; push_cast; linarith [a.2, b.2, c.2]

/-- **exponent certificate**: `s_b / W_b < 125000 ^ (1 - a)`, `a = 325/10¹¹` -/
theorem bit_exponent :
    ((s : ℕ) : ℝ) / (W : ℕ) < (125000 : ℝ) ^ (1 - (aB : ℝ)) := by
  obtain ⟨-, -, -, hW, -, -, hs, -⟩ := counts
  rw [hs, hW, show ((aB : ℚ) : ℝ) = 325 / 10 ^ 11 by norm_num [aB]]
  apply exponent_certificate 125000 (11737 / 1000) (325 / 10 ^ 11) (49 / 1284490000) _
    (by norm_num) (by norm_num) log_125000
  · norm_num
  · norm_num

/-- the same network certifies `1 - τ = 325018/10¹⁴` (`(1 - τ) · 11737/1000 ≤ η_b`; used in
section C) -/
theorem bit_exponent_325018 :
    ((s : ℕ) : ℝ) / (W : ℕ) < (125000 : ℝ) ^ (1 - (325018 / 10 ^ 14 : ℝ)) := by
  obtain ⟨-, -, -, hW, -, -, hs, -⟩ := counts
  rw [hs, hW]
  apply exponent_certificate 125000 (11737 / 1000) (325018 / 10 ^ 14) (49 / 1284490000) _
    (by norm_num) (by norm_num) log_125000
  · norm_num
  · norm_num

/-! ## B. The witness κ = 1624/10¹² -/

/-- the guard is that of the unchanged compressed complex network (PR #5) -/
theorem guard_constants :
    PR5.Eg = 338201706233372774319082463160146840064 ∧  -- json aligned-bit-network.json witness.guard.E
    PR5.Bg = 338201706233372774319109678801287590064 ∧  -- json aligned-bit-network.json witness.guard.B
    PR5.C0n = 321727027889740762489223803495350305328695729120143793284991524019954162292886152000000 ∧  -- json aligned-bit-network.json witness.guard.C0
    PR5.m = 15625 ∧  -- json aligned-bit-network.json witness.guard.m
    PR5.s = 27215641140750000  -- json aligned-bit-network.json witness.guard.s
    := by
  exact ⟨PR5.guard_constants.1, PR5.guard_constants.2.1, rfl, PR5.counts.2.1,
    PR5.counts.2.2.2.2.2.2.1⟩

def P : Params where
  τ := 3999999987 / 4000000000  -- json aligned-bit-network.json witness.parameters.tau
  σ := 499999993 / 500000000  -- json aligned-bit-network.json witness.parameters.sigma
  ε := 49999 / 100000  -- json aligned-bit-network.json witness.parameters.epsilon
  c := 9999 / 10000  -- json aligned-bit-network.json witness.parameters.c
  lam := 1999999993501 / 2000000000000  -- json aligned-bit-network.json witness.parameters.lam
  lamp := 999999996751 / 1000000000000  -- json aligned-bit-network.json witness.parameters.lamp
  κ := 203 / 125000000000  -- json aligned-bit-network.json witness.parameters.kappa
  β := 19 / 25  -- json aligned-bit-network.json witness.parameters.beta
  δ := 1 / 1000000  -- json aligned-bit-network.json witness.parameters.delta
  C1 := 19601 / 10000  -- json aligned-bit-network.json witness.parameters.C1

/-- the parameters of `notes/aligned-bit-note.tex` lines 44-47 -/
theorem parameter_origin :
    P.τ = 1 - 325 / 10 ^ 11 ∧ P.σ = 1 - 14 / 10 ^ 9 ∧ P.lam = 1 - 32495 / 10 ^ 13 ∧
    P.lamp = 1 - 3249 / 10 ^ 12 ∧ P.κ = 1624 / 10 ^ 12 ∧ P.C1 = 5 - 4 * P.β + PR5.ζ ∧
    PR5.ζ = 1 / 10000 ∧  -- json aligned-bit-network.json witness.guard.zeta
    P.β = 19 / 25 ∧  -- json aligned-bit-network.json witness.guard.beta
    P.C1 = 19601 / 10000 ∧  -- json aligned-bit-network.json witness.guard.C1
    1 - P.τ = 13 / 4000000000 ∧  -- json aligned-bit-network.json bit_saving
    1 - P.σ = 7 / 500000000 ∧  -- json aligned-bit-network.json complex_saving
    1 - P.τ = aB ∧ 1 - P.σ = PR5.aC ∧
    -- PR #5's bit saving, which this network replaces
    1 - PR5.Fast.P.τ = 37 / 12500000000  -- json aligned-bit-network.json previous_bit_saving
    := by
  norm_num [P, PR5.ζ, aB, PR5.aC, PR5.Fast.P]

/-- `τ` is certified by the aligned network, `σ` by PR #5's complex network -/
theorem exponents_certified :
    ((s : ℕ) : ℝ) / (W : ℕ) < (125000 : ℝ) ^ ((P.τ : ℚ) : ℝ) ∧
    ((PR5.s : ℕ) : ℝ) / (PR5.W : ℕ) < (15625 : ℝ) ^ ((P.σ : ℚ) : ℝ) := by
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - (aB : ℝ) := by
    rw [show P.τ = 1 - aB by norm_num [P, aB]]; push_cast; ring
  have hσ : ((P.σ : ℚ) : ℝ) = 1 - (PR5.aC : ℝ) := by
    rw [show P.σ = 1 - PR5.aC by norm_num [P, PR5.aC]]; push_cast; ring
  rw [hτ, hσ]; exact ⟨bit_exponent, PR5.complex_exponent⟩

theorem recurrence_values :
    P.internal = 3999999987 / 4000000000 ∧  -- json aligned-bit-network.json witness.recurrence.internal
    P.leaf = 6249999979 / 6250000000 ∧  -- json aligned-bit-network.json witness.recurrence.leaf
    P.prep = 1 / 10000 ∧  -- json aligned-bit-network.json witness.recurrence.preprocessing
    P.layer = 3999999987 / 4000000000  -- json aligned-bit-network.json witness.recurrence.layer
    := by
  norm_num [P, Params.internal, Params.leaf, Params.prep, Params.layer]

theorem slack_values :
    P.ε * P.c = 499940001 / 1000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.K_dominates_log_p
    1 - P.ε - P.ε * P.c = 69999 / 1000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.K_smaller_than_ell
    1 - 2 * P.ε = 1 / 50000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.alpha_squared_theta_growth
    1 - P.β = 6 / 25 ∧  -- json aligned-bit-network.json witness.constraint_slacks.beta_below_one
    P.β = 19 / 25 ∧  -- json aligned-bit-network.json witness.constraint_slacks.beta_positive
    P.c = 9999 / 10000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.c_positive
    1 - P.τ - P.ε * (1 - P.τ) = 650013 / 400000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.crt_layout
    1 / 8 - P.δ = 124999 / 1000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.delta_below_one_eighth
    P.δ = 1 / 1000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.delta_positive
    P.ε = 49999 / 100000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.epsilon_positive
    1 - P.δ - 2 * P.ε = 19 / 1000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.gaussian_cost
    1 - P.ε * P.C1 = 19969601 / 1000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.guard_width
    P.κ = 203 / 125000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.kappa_positive
    P.lam - P.σ = 21501 / 2000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.lambda_above_sigma
    P.lam - P.τ = 1 / 2000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.lambda_above_tau
    1 - P.lam = 6499 / 2000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.lambda_below_one
    P.lamp - P.lam = 1 / 2000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.lambda_prime_above_lambda
    1 - P.lamp = 3249 / 1000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.lambda_prime_below_one
    P.lamp - (P.σ + P.β * (1 - P.σ)) = 111 / 1000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.leaf_cost
    P.lam - P.internal = 1 / 2000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.packed_overhead
    1 - P.ε * (1 + P.c) = 69999 / 1000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.prefix_cost
    1 - 2 * P.ε = 1 / 50000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.prime_interval_growth
    1 - P.ε = 50001 / 100000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.r_superpolynomial
    P.lamp - P.prep = 999899996751 / 1000000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.reserved_axes
    1 - P.δ - P.ε = 500009 / 1000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.scalar_cost
    1 - P.σ = 7 / 500000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.sigma_below_one
    P.σ = 499999993 / 500000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.sigma_positive
    1 - P.τ = 13 / 4000000000 ∧  -- json aligned-bit-network.json witness.constraint_slacks.tau_below_one
    P.τ = 3999999987 / 4000000000  -- json aligned-bit-network.json witness.constraint_slacks.tau_positive
    := by
  norm_num [P, Params.internal, Params.prep]

theorem constraint_slacks :
    0 < P.ε * P.c ∧  -- K_dominates_log_p
    0 < 1 - P.ε - P.ε * P.c ∧  -- K_smaller_than_ell
    0 < 1 - 2 * P.ε ∧  -- alpha_squared_theta_growth
    0 < 1 - P.β ∧  -- beta_below_one
    0 < P.β ∧  -- beta_positive
    0 < P.c ∧  -- c_positive
    0 < 1 - P.τ - P.ε * (1 - P.τ) ∧  -- crt_layout
    0 < 1 / 8 - P.δ ∧  -- delta_below_one_eighth
    0 < P.δ ∧  -- delta_positive
    0 < P.ε ∧  -- epsilon_positive
    0 < 1 - P.δ - 2 * P.ε ∧  -- gaussian_cost
    0 < 1 - P.ε * P.C1 ∧  -- guard_width
    0 < P.κ ∧  -- kappa_positive
    0 < P.lam - P.σ ∧  -- lambda_above_sigma
    0 < P.lam - P.τ ∧  -- lambda_above_tau
    0 < 1 - P.lam ∧  -- lambda_below_one
    0 < P.lamp - P.lam ∧  -- lambda_prime_above_lambda
    0 < 1 - P.lamp ∧  -- lambda_prime_below_one
    0 < P.lamp - (P.σ + P.β * (1 - P.σ)) ∧  -- leaf_cost
    0 < P.lam - P.internal ∧  -- packed_overhead
    0 < 1 - P.ε * (1 + P.c) ∧  -- prefix_cost
    0 < 1 - 2 * P.ε ∧  -- prime_interval_growth
    0 < 1 - P.ε ∧  -- r_superpolynomial
    0 < P.lamp - P.prep ∧  -- reserved_axes
    0 < 1 - P.δ - P.ε ∧  -- scalar_cost
    0 < 1 - P.σ ∧  -- sigma_below_one
    0 < P.σ ∧  -- sigma_positive
    0 < 1 - P.τ ∧  -- tau_below_one
    0 < P.τ  -- tau_positive
    := by
  norm_num [P, Params.internal, Params.prep]

theorem margin_values :
    P.g1 = 69999 / 1000000000 ∧  -- json aligned-bit-network.json witness.margins.g1
    P.g2 = 6499220013 / 4000000000000000000 ∧  -- json aligned-bit-network.json witness.margins.g2
    P.g3 = 162446751 / 100000000000000000 ∧  -- json aligned-bit-network.json witness.margins.g3
    P.g4 = 650013 / 400000000000000 ∧  -- json aligned-bit-network.json witness.margins.g4
    P.g5fast = 19 / 1000000 ∧  -- json aligned-bit-network.json witness.margins.g5
    P.g6 = 500009 / 1000000 ∧  -- json aligned-bit-network.json witness.margins.g6
    P.g7 = 49999 / 100000  -- json aligned-bit-network.json witness.margins.g7
    := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- **headline**: `g3 = 162446751/10¹⁷` is the minimum margin, `κ = 1624/10¹²` is below it
by `46751/10¹⁷`, and `2^-30 < κ < 2^-29` -/
theorem kappa_witness :
    P.g3 ≤ P.g1 ∧ P.g3 ≤ P.g2 ∧ P.g3 ≤ P.g4 ∧ P.g3 ≤ P.g5fast ∧ P.g3 ≤ P.g6 ∧ P.g3 ≤ P.g7 ∧
    P.g3 = 162446751 / 100000000000000000 ∧  -- json aligned-bit-network.json witness.minimum_margin
    P.g3 - P.κ = 46751 / 100000000000000000 ∧  -- json aligned-bit-network.json witness.absorption_gap
    P.κ < P.g3 ∧ (1 : ℚ) / 2 ^ 30 < P.κ ∧ P.κ < 1 / 2 ^ 29 := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- note lines 48-56 and the README ratios -/
theorem note_lines :
    P.σ < P.τ ∧ P.internal = P.τ ∧ max (max P.τ P.σ) P.internal < P.lam ∧ P.lam < P.lamp ∧
    P.lamp < 1 ∧ max (P.σ + P.β * (1 - P.σ)) (1 - P.c) < P.lamp ∧
    P.ε * P.C1 = 980030399 / 10 ^ 9 ∧ P.ε * P.C1 < 1 ∧ 3 / 4 < P.β ∧
    (1 - P.β) * (14 / 10 ^ 9) = 336 / 10 ^ 11 ∧ 1 - P.lamp < (1 - P.β) * (14 / 10 ^ 9) ∧
    P.g3 = P.ε * (1 - P.lamp) ∧
    P.κ / (1479 / 10 ^ 12) = 56 / 51 ∧  -- json aligned-bit-network.json improvement_over_fast_gaussian
    (109 : ℚ) / 100 < P.κ / (1479 / 10 ^ 12) ∧ P.κ / (1479 / 10 ^ 12) < 110 / 100 ∧
    (275 : ℚ) / 100 < P.κ / (59 / 10 ^ 11) ∧ P.κ / (59 / 10 ^ 11) < 276 / 100 ∧
    (195 : ℚ) / 10 < P.κ / (83 / 10 ^ 12) ∧ P.κ / (83 / 10 ^ 12) < 197 / 10 := by
  norm_num [P, Params.internal, Params.g3]

/-- "The scoped ceiling for this bit network is κ < a/2 < 2^-29" -/
theorem ceiling_values :
    (325 : ℚ) / 10 ^ 11 / 2 = 13 / 8000000000 ∧
    (325 : ℚ) / 10 ^ 11 / 2 < 1 / 2 ^ 29 ∧ 999 / 1000 * ((325 : ℚ) / 10 ^ 11 / 2) < P.κ := by
  norm_num [P]

/-- the stated ceiling `κ < a/2`, **for τ fixed at `P.τ = 1 - a`**; not a ceiling for the
published network (section C) -/
theorem scoped_ceiling (ε' lamp' κ' : ℝ) (hl : ((P.τ : ℚ) : ℝ) < lamp') (hε : 0 < ε')
    (h3 : κ' < ε' * (1 - lamp')) (h4 : κ' < (1 - ((P.τ : ℚ) : ℝ)) * (1 - ε')) :
    κ' < 13 / 8000000000 := by  -- json aligned-bit-network.json scoped_ceiling.upper
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - 325 / 10 ^ 11 := by norm_num [P]
  rw [hτ] at hl h4
  have := ceiling_half (1 - 325 / 10 ^ 11) ε' lamp' κ' (by norm_num) hl hε h3 h4
  linarith

/-- the JSON scope string "g2,g3,g4 <= a_b*min(eps,1-eps)" fails for `g4` alone -/
theorem g4_exceeds_a_min :
    (1 - P.τ) * min P.ε (1 - P.ε) < P.g4 ∧ P.g2 ≤ (1 - P.τ) * min P.ε (1 - P.ε) ∧
    P.g3 ≤ (1 - P.τ) * min P.ε (1 - P.ε) := by
  norm_num [P, Params.g2, Params.g3, Params.g4, min_def]

/-- `docs/research/aligned-bit.md`: "A further 3% on a_b would close this window".
With the guard (`ε = 49999/100000`, `ζ = 1/10⁴`) every admissible `β` has
`(1-β)a_c < 1.077·a`, so a bit saving above `1.077·a` closes the leaf/guard window; but
`β = 7501/10000` still meets the guard with `(1-β)a_c > 1.07·a`, so a 3% (indeed 7%)
larger `a` does **not** close it. The 3% figure holds only at the chosen `β = 19/25`. -/
theorem window_size :
    (∀ β' : ℝ, (49999 / 100000 : ℝ) * (5 - 4 * β' + 1 / 10000) < 1 →
      (1 - β') * (14 / 10 ^ 9) < 1077 / 1000 * (325 / 10 ^ 11)) ∧
    (49999 / 100000 : ℚ) * (5 - 4 * (7501 / 10000) + 1 / 10000) < 1 ∧
    107 / 100 * ((325 : ℚ) / 10 ^ 11) < (1 - 7501 / 10000) * (14 / 10 ^ 9) ∧
    (1 - (19 : ℚ) / 25) * (14 / 10 ^ 9) < 104 / 100 * (325 / 10 ^ 11) := by
  refine ⟨fun β' h => by linarith, by norm_num, by norm_num, by norm_num⟩

/-! ## C. The ceiling for the published aligned network -/

namespace Certified

/-- an admissible fast-Gaussian choice (audit witness): PR #6's `σ`, `β`, `C1`, and a `τ` the
same aligned network certifies (`bit_exponent_325018`) -/
def Pw : Params :=
  { P with
    τ := 1 - 325018 / 10 ^ 14  -- audit
    lam := 1 - 3250175 / 10 ^ 15  -- audit
    lamp := 1 - 325017 / 10 ^ 14  -- audit
    ε := 4999999 / 10 ^ 7  -- audit
    c := 1  -- audit
    δ := 1 / 10 ^ 8  -- audit
    κ := 162508 / 10 ^ 14 }  -- audit

theorem Pw_tau_certified : ((s : ℕ) : ℝ) / (W : ℕ) < (125000 : ℝ) ^ ((Pw.τ : ℚ) : ℝ) := by
  have h : ((Pw.τ : ℚ) : ℝ) = 1 - 325018 / 10 ^ 14 := by norm_num [Pw, P]
  rw [h]; exact bit_exponent_325018

/-- negative control for `scoped_ceiling`: all 29 slacks and seven margins hold, with the
guard `C1 = 5 - 4β + ζ` and the certified `σ`, at `κ = 162508/10¹⁴ > a/2` -/
theorem fixed_tau_ceiling_beaten :
    Pw.FastOK ∧ Pw.FastAbsorbs ∧ Pw.C1 = 5 - 4 * Pw.β + PR5.ζ ∧ Pw.σ = P.σ ∧
    (13 / 8000000000 : ℚ) < Pw.κ := by
  unfold Params.FastOK Params.FastAbsorbs
  norm_num [Pw, P, PR5.ζ, Params.internal, Params.prep, Params.g1, Params.g2, Params.g3,
    Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- **the ceiling for this network**: every `τ` it certifies, with `τ < λ' < 1`, `ε > 0` and
`κ` below `g3` and `g4`, gives `κ < 16254/10¹³ < 2^-29` -/
theorem certified_ceiling (τ' ε' lamp' κ' : ℝ)
    (hcert : ((s : ℕ) : ℝ) / (W : ℕ) ≤ (125000 : ℝ) ^ τ') (hl : τ' < lamp') (hl1 : lamp' < 1)
    (hε : 0 < ε') (h3 : κ' < ε' * (1 - lamp')) (h4 : κ' < (1 - τ') * (1 - ε')) :
    κ' < 16254 / 10 ^ 13 ∧ κ' < 1 / 2 ^ 29 := by
  have hk := ceiling_half τ' ε' lamp' κ' (by linarith) hl hε h3 h4
  obtain ⟨-, -, -, hW, -, -, hs, -⟩ := counts
  rw [hs, hW] at hcert
  have hsv := certified_saving_le 125000 ((49344965957616000000 : ℝ) / 394759742720000) τ'
    (by norm_num) (by norm_num) hcert
  have hpos : 0 < 1 - τ' := by linarith
  have : (1 - τ') * (117349 / 10000) < (1 - τ') * Real.log 125000 :=
    mul_lt_mul_of_pos_left log_125000_gt hpos
  norm_num at hsv this ⊢
  constructor <;> linarith

/-- non-vacuity and tightness: the witness meets every hypothesis of `certified_ceiling`, so no
ceiling below `162508/10¹⁴` holds; the stated one is `32/10¹⁴` above it -/
theorem certified_ceiling_attained :
    ((Pw.κ : ℚ) : ℝ) < 16254 / 10 ^ 13 ∧ (16254 / 10 ^ 13 : ℚ) - Pw.κ = 32 / 10 ^ 14 := by
  refine ⟨(certified_ceiling (Pw.τ : ℝ) (Pw.ε : ℝ) (Pw.lamp : ℝ) (Pw.κ : ℝ)
    Pw_tau_certified.le ?_ ?_ ?_ ?_ ?_).1, by norm_num [Pw, P]⟩ <;>
    norm_num [Pw, P]

end Certified

end PRChecksB.PR6
