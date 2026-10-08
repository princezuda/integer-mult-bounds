import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The copied-centre lemma

Two versions:

* `notes/copied-centers-lemma.tex` (retained centres, used by the selected witness): a
  retained centre at `D_U` with `dim U = r` changes its rank profile from `z^r + z^h` to
  `z^r + z^(h-r)`, in both invocation orientations;
* `research/swapnil-parallel/upstream/notes/copied-centres.tex` (direct centres): the frame
  path `D₀ → D₁ → D₀ → D₁` (ranks `h, h, h`) becomes `D₀ → D₁` for the original plus
  `D₁ → D₀` for the copy (ranks `h, h`).

**Model.** A role's physical stream holds `F_Q w`, where `w` is its scalar value and
`F_Q` is the (invertible, linear) address frame of `Q`; changing frame applies
`F_{Q₂} F_{Q₁}⁻¹`. A pointwise scalar gate acts on streams that share one frame. Scatter
reads are gates that do not change the centre, and no other gate touches the centre
between them: these are the lemma's hypotheses, and they are built into the old
schedules below. A fresh zero stream is `0` in every frame.

**What is proved.**
* Section 1: each copied schedule produces exactly the old schedule's streams, for every
  input and arbitrary dirty values. For direct centres the action is also computed: the
  targets gain the gathered sum and the centre is restored. For retained centres the
  restoration is that of the old schedule, which is unchanged.
* Section 2: from the subspace construction (`E_U ⊕ E_{U⊥} = E_F`, `D₀ ∩ E_F = 0`) every
  individual charge, and that each new original edge has residual `E_{U⊥} = P ⊗ U⊥`.
* Section 3: the histogram update and, summed over invocations, the rank-mass drop `L`.

**Not proved here.** Charges are `|Δ dim|`, as in the note ("a local change of rank `d`
has ambient rank `d`"). That the new residual `P ⊗ U⊥` admits the required basis (an
orthonormal one over `𝔽₂`, a rational partial swap in the bit network) is the note's
claim and is not formalized. Neither are the batched profile of the copy's move (it is the
old edge's matrix) and the tape schedule.
-/

namespace KappaCheck.CopiedCentres

open Module

/-! ## 1. Scalar action -/

section Scalar

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (F : ι → M ≃ₗ[R] M)

/-- change a physical stream from frame `q₁` to frame `q₂` -/
def move (q₁ q₂ : ι) (s : M) : M := F q₂ ((F q₁).symm s)

@[simp] theorem move_frame (q₁ q₂ : ι) (w : M) : move F q₁ q₂ (F q₁ w) = F q₂ w := by
  simp [move]

theorem move_move (q₁ q₂ q₃ : ι) (s : M) :
    move F q₂ q₃ (move F q₁ q₂ s) = move F q₁ q₃ s := by
  simp [move]

/-- a pointwise gate commutes with a frame: `F (u + a • v) = F u + a • F v` -/
theorem gate_frame (q : ι) (a : R) (u v : M) : F q (u + a • v) = F q u + a • F q v := by
  simp

variable {n n' : ℕ}

/-- **Direct centres, old word** (`copied-centres.tex` lines 14-17). Sources `xs` at the
gather frame `D₁`, targets `ys` at the scatter frame `D₀`, the centre `pc` starting at
`D₀`: scatter the old value, rise, gather, return (rank `h`), scatter the new value,
re-rise (rank `h`), cleanup gather. -/
def directOld (D₀ D₁ : ι) (k : Fin n' → R) (l : Fin n → R) (xs : Fin n' → M)
    (ys : Fin n → M) (pc : M) : (Fin n' → M) × (Fin n → M) × M :=
  let ys₁ := fun j => ys j - l j • pc
  let pc₁ := move F D₀ D₁ pc
  let pc₂ := pc₁ + ∑ i, k i • xs i
  let pc₃ := move F D₁ D₀ pc₂
  let ys₂ := fun j => ys₁ j + l j • pc₃
  let pc₄ := move F D₀ D₁ pc₃
  let pc₅ := pc₄ - ∑ i, k i • xs i
  (xs, ys₂, pc₅)

/-- **Direct centres, copied word** (lines 19-25): after the first gather copy the centre
into a fresh zero stream at `D₁`, move only the copy to `D₀`, read it, erase it; the
original stays at `D₁`. -/
def directCopied (D₀ D₁ : ι) (k : Fin n' → R) (l : Fin n → R) (xs : Fin n' → M)
    (ys : Fin n → M) (pc : M) : (Fin n' → M) × (Fin n → M) × M :=
  let ys₁ := fun j => ys j - l j • pc
  let pc₁ := move F D₀ D₁ pc
  let pc₂ := pc₁ + ∑ i, k i • xs i
  let pt₂ := move F D₁ D₀ ((0 : M) + pc₂)
  let ys₂ := fun j => ys₁ j + l j • pt₂
  let pc₅ := pc₂ - ∑ i, k i • xs i
  (xs, ys₂, pc₅)

/-- the copied word produces exactly the old streams, for every input -/
theorem direct_same (D₀ D₁ : ι) (k : Fin n' → R) (l : Fin n → R) (xs : Fin n' → M)
    (ys : Fin n → M) (pc : M) :
    directCopied F D₀ D₁ k l xs ys pc = directOld F D₀ D₁ k l xs ys pc := by
  simp [directCopied, directOld, move]

/-- its action: target `j` gains `l_j Σ kᵢ xᵢ`, and an arbitrary centre value `c` is
restored (ending at `D₁`) -/
theorem direct_action (D₀ D₁ : ι) (k : Fin n' → R) (l : Fin n → R) (x : Fin n' → M)
    (y : Fin n → M) (c : M) :
    directCopied F D₀ D₁ k l (fun i => F D₁ (x i)) (fun j => F D₀ (y j)) (F D₀ c) =
      ((fun i => F D₁ (x i)), (fun j => F D₀ (y j + l j • ∑ i, k i • x i)), F D₁ c) := by
  have hsum : (∑ i, k i • (F D₁) (x i)) = F D₁ (∑ i, k i • x i) := by
    rw [map_sum]; simp only [map_smul]
  simp only [directCopied, move_frame, zero_add, hsum, ← map_add, Prod.mk.injEq, true_and]
  constructor
  · funext j
    simp only [map_add, map_sub, map_smul, smul_add]
    abel
  · simp

/-- **Retained centres, forward orientation** (`copied-centers-lemma.tex` lines 45-48): the
centre at `D_U` moves to `D₀` (rank `r`), feeds the scatter reads, then moves to `D₁`
(rank `h`) for its cleanup `cont`. -/
def forwardOld (DU D₀ D₁ : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pc₁ := move F DU D₀ pc
  let ys' := fun j => ys j + l j • pc₁
  (ys', cont (move F D₀ D₁ pc₁))

/-- forward copied schedule (lines 49-56): copy at `D_U`, move only the copy to `D₀`
(rank `r`), read it, erase it, and move the original directly `D_U → D₁` (rank `h - r`) -/
def forwardCopied (DU D₀ D₁ : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pt := move F DU D₀ ((0 : M) + pc)
  let ys' := fun j => ys j + l j • pt
  (ys', cont (move F DU D₁ pc))

/-- the forward copied schedule produces exactly the old streams. Since the reads do not
change the centre, this reduces to path independence of frame changes (`move_move`). -/
theorem forward_same (DU D₀ D₁ : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    forwardCopied F DU D₀ D₁ l cont ys pc = forwardOld F DU D₀ D₁ l cont ys pc := by
  simp [forwardCopied, forwardOld, move_move]

/-- **Retained centres, reverse orientation** (lines 58-66): the centre at `D₀` moves to
`D₁` (rank `h`), feeds the scatter reads, then moves to `D_{U⊥}` (rank `r`). -/
def reverseOld (D₀ D₁ DUp : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pc₁ := move F D₀ D₁ pc
  let ys' := fun j => ys j + l j • pc₁
  (ys', cont (move F D₁ DUp pc₁))

/-- reverse copied schedule: advance the original directly `D₀ → D_{U⊥}` (rank `h - r`),
copy it there, move the copy to `D₁` (rank `r`), read it, erase it -/
def reverseCopied (D₀ D₁ DUp : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pc₁ := move F D₀ DUp pc
  let pt := move F DUp D₁ ((0 : M) + pc₁)
  let ys' := fun j => ys j + l j • pt
  (ys', cont pc₁)

theorem reverse_same (D₀ D₁ DUp : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    reverseCopied F D₀ D₁ DUp l cont ys pc = reverseOld F D₀ D₁ DUp l cont ys pc := by
  simp [reverseCopied, reverseOld, move_move]

end Scalar

/-! ## 2. Rank charges from the frame construction -/

section Rank

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- the rank charged for changing between two frames: `|dim Q₂ - dim Q₁|` -/
noncomputable def charge (Q₁ Q₂ : Submodule K V) : ℕ :=
  Int.natAbs ((finrank K Q₂ : ℤ) - finrank K Q₁)

/-- `dim (D ⊔ E) = dim D + dim E` when `D ⊓ E = ⊥` -/
theorem finrank_sup_of_disjoint (D E : Submodule K V) (h : D ⊓ E = ⊥) :
    finrank K ↥(D ⊔ E) = finrank K D + finrank K E := by
  have := Submodule.finrank_sup_add_finrank_inf_eq D E
  rw [h, finrank_bot, add_zero] at this
  exact this

/-- One invocation's frames (lines 15-22): `E_F = P ⊗ F` splits as `E_U ⊕ E_{U⊥}` with
`E_U = P ⊗ U` and `E_{U⊥} = P ⊗ U⊥`, and `E_F` meets `D₀ = B ⊗ F` only in `0`. In the note
these sums are orthogonal; only the independence they imply is used here. -/
structure Frames (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  D₀ : Submodule K V
  EU : Submodule K V
  EUp : Submodule K V
  EF : Submodule K V
  split : EU ⊔ EUp = EF
  splitDisj : EU ⊓ EUp = ⊥
  disj : D₀ ⊓ EF = ⊥

variable (f : Frames K V)

def Frames.DU := f.D₀ ⊔ f.EU
def Frames.DUp := f.D₀ ⊔ f.EUp
def Frames.D₁ := f.D₀ ⊔ f.EF

omit [FiniteDimensional K V] in
theorem Frames.hU : f.EU ≤ f.EF := f.split ▸ le_sup_left

omit [FiniteDimensional K V] in
theorem Frames.hUp : f.EUp ≤ f.EF := f.split ▸ le_sup_right

/-- `dim U⊥ = h - r`: derived from the split, not assumed -/
theorem Frames.dim_EUp : finrank K f.EUp = finrank K f.EF - finrank K f.EU := by
  have h := finrank_sup_of_disjoint f.EU f.EUp f.splitDisj
  rw [f.split] at h
  omega

theorem Frames.dim_DU : finrank K f.DU = finrank K f.D₀ + finrank K f.EU :=
  finrank_sup_of_disjoint _ _ (le_bot_iff.1 (f.disj ▸ inf_le_inf_left _ f.hU))

theorem Frames.dim_DUp : finrank K f.DUp = finrank K f.D₀ + finrank K f.EUp :=
  finrank_sup_of_disjoint _ _ (le_bot_iff.1 (f.disj ▸ inf_le_inf_left _ f.hUp))

theorem Frames.dim_D₁ : finrank K f.D₁ = finrank K f.D₀ + finrank K f.EF :=
  finrank_sup_of_disjoint _ _ f.disj

omit [FiniteDimensional K V] in
/-- the frames are nested: `D₀ ≤ D_U ≤ D₁` and `D₀ ≤ D_{U⊥} ≤ D₁` -/
theorem Frames.nested : f.D₀ ≤ f.DU ∧ f.DU ≤ f.D₁ ∧ f.D₀ ≤ f.DUp ∧ f.DUp ≤ f.D₁ :=
  ⟨le_sup_left, sup_le_sup_left f.hU _, le_sup_left, sup_le_sup_left f.hUp _⟩

/-- **The new edges' residual**: `E_{U⊥}` is a complement of `D_U` in `D₁`, and of `D₀` in
`D_{U⊥}`. So the original's direct moves `D_U → D₁` (forward) and `D₀ → D_{U⊥}` (reverse)
have residual `P ⊗ U⊥`. That this residual admits the required basis is the note's claim
and is not proved here. -/
theorem Frames.new_residual :
    f.DU ⊔ f.EUp = f.D₁ ∧ f.DU ⊓ f.EUp = ⊥ ∧ f.D₀ ⊔ f.EUp = f.DUp := by
  refine ⟨?_, ?_, rfl⟩
  · simp only [Frames.DU, Frames.D₁, sup_assoc, f.split]
  · have hsup : f.DU ⊔ f.EUp = f.D₁ := by simp only [Frames.DU, Frames.D₁, sup_assoc, f.split]
    have h := Submodule.finrank_sup_add_finrank_inf_eq f.DU f.EUp
    rw [hsup, f.dim_D₁, f.dim_DU, f.dim_EUp] at h
    have hle : finrank K f.EU ≤ finrank K f.EF := Submodule.finrank_mono f.hU
    have h0 : finrank K ↥(f.DU ⊓ f.EUp) = 0 := by omega
    exact Submodule.finrank_eq_zero.1 h0

/-- **Forward orientation, every charge**: old path `D_U → D₀ → D₁` charges `r` then `h`;
the copy's `D_U → D₀` charges `r` and the original's `D_U → D₁` charges `h - r`, so the
profile `z^r + z^h` becomes `z^r + z^(h-r)` (lines 37-43). -/
theorem forward_profile :
    charge f.DU f.D₀ = finrank K f.EU ∧ charge f.D₀ f.D₁ = finrank K f.EF ∧
    charge f.DU f.D₁ = finrank K f.EF - finrank K f.EU := by
  have hle : finrank K f.EU ≤ finrank K f.EF := Submodule.finrank_mono f.hU
  simp only [charge, f.dim_DU, f.dim_D₁]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **Reverse orientation, every charge**: old path `D₀ → D₁ → D_{U⊥}` charges `h` then `r`;
the original's `D₀ → D_{U⊥}` charges `h - r` and the copy's `D_{U⊥} → D₁` charges `r`. -/
theorem reverse_profile :
    charge f.D₀ f.D₁ = finrank K f.EF ∧ charge f.D₁ f.DUp = finrank K f.EU ∧
    charge f.D₀ f.DUp = finrank K f.EF - finrank K f.EU ∧
    charge f.DUp f.D₁ = finrank K f.EU := by
  have hle : finrank K f.EU ≤ finrank K f.EF := Submodule.finrank_mono f.hU
  simp only [charge, f.dim_DUp, f.dim_D₁, f.dim_EUp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **Direct centres, every charge**: each of `D₀ → D₁` and `D₁ → D₀` charges `h`, so the
old path `D₀ → D₁ → D₀ → D₁` has three rank-`h` children and the copied schedule two
(`copied-centres.tex` lines 22-24). -/
theorem direct_profile :
    charge f.D₀ f.D₁ = finrank K f.EF ∧ charge f.D₁ f.D₀ = finrank K f.EF := by
  simp only [charge, f.dim_D₁]
  constructor <;> omega

/-! ### Non-vacuity: a frame system with `0 < r < h` -/

section Witness

open LinearMap in
/-- `V = ℚ × ℚ²`: `D₀ = ℚ × 0`, `E_F = 0 × ℚ²`, and `E_U`, `E_{U⊥}` its two coordinate lines -/
noncomputable def witness : Frames ℚ (ℚ × (ℚ × ℚ)) where
  D₀ := range (inl ℚ ℚ (ℚ × ℚ))
  EU := range ((inr ℚ ℚ (ℚ × ℚ)).comp (inl ℚ ℚ ℚ))
  EUp := range ((inr ℚ ℚ (ℚ × ℚ)).comp (inr ℚ ℚ ℚ))
  EF := range (inr ℚ ℚ (ℚ × ℚ))
  split := by
    rw [range_comp, range_comp, ← Submodule.map_sup, sup_range_inl_inr, Submodule.map_top]
  splitDisj := by
    rw [range_comp, range_comp, ← Submodule.map_inf _ inr_injective,
      (disjoint_inl_inr (R := ℚ) (M := ℚ) (M₂ := ℚ)).eq_bot, Submodule.map_bot]
  disj := (disjoint_inl_inr (R := ℚ) (M := ℚ) (M₂ := ℚ × ℚ)).eq_bot

theorem witness_dims : finrank ℚ witness.EF = 2 ∧ finrank ℚ witness.EU = 1 := by
  constructor
  · show finrank ℚ (LinearMap.range (LinearMap.inr ℚ ℚ (ℚ × ℚ))) = 2
    rw [LinearMap.finrank_range_of_inj LinearMap.inr_injective]; simp
  · show finrank ℚ (LinearMap.range ((LinearMap.inr ℚ ℚ (ℚ × ℚ)).comp (LinearMap.inl ℚ ℚ ℚ))) = 1
    rw [LinearMap.finrank_range_of_inj (f := (LinearMap.inr ℚ ℚ (ℚ × ℚ)).comp (LinearMap.inl ℚ ℚ ℚ))
      (by intro a b hab; simpa using hab)]; simp

/-- on the witness both profiles fire with `r = 1`, `h = 2` -/
theorem witness_profiles :
    charge witness.DU witness.D₀ = 1 ∧ charge witness.DU witness.D₁ = 1 ∧
    charge witness.D₁ witness.DUp = 1 ∧ charge witness.D₀ witness.DUp = 1 := by
  obtain ⟨hF, hU⟩ := witness_dims
  obtain ⟨f1, -, f3⟩ := forward_profile witness
  obtain ⟨-, r2, r3, -⟩ := reverse_profile witness
  exact ⟨by rw [f1, hU], by rw [f3, hF, hU], by rw [r2, hU], by rw [r3, hF, hU]⟩

end Witness

end Rank

/-! ## 3. Histogram and rank mass -/

section Mass

open Finset

/-- **Lines 79-86**: with `r = h - 1`, each of the `h` retained centres of an invocation
turns one rank-`h` child into a rank-one child, so the invocation's rank mass drops by
`ℓ_h = h(h-1)`. -/
theorem histogram_update (H : ℕ → ℤ) (h n : ℕ) (h1 : 1 < h) (hn : h < n) :
    ∑ r ∈ range n, (r : ℤ) * (H r + (if r = 1 then (h : ℤ) else 0) - (if r = h then (h : ℤ) else 0)) =
      ∑ r ∈ range n, (r : ℤ) * H r - h * (h - 1) := by
  have e : ∀ r : ℕ, (r : ℤ) * (H r + (if r = 1 then (h : ℤ) else 0) - (if r = h then (h : ℤ) else 0)) =
      r * H r + (if r = 1 then (r : ℤ) * h else 0) - (if r = h then (r : ℤ) * h else 0) := by
    intro r; rw [mul_sub, mul_add, mul_ite, mul_ite, mul_zero]
  simp only [e, sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_range]
  rw [if_pos (by omega), if_pos hn]
  push_cast
  ring

/-- the updated histogram of one invocation -/
def updated (H : ℕ → ℤ) (h : ℕ) (r : ℕ) : ℤ :=
  H r + (if r = 1 then (h : ℤ) else 0) - (if r = h then (h : ℤ) else 0)

/-- **Lines 92-100, derived**: two factors `a, b`, with `v_b` invocations of factor `a`
(local histogram `Hₐ`) and `v_a` of factor `b`. Every other child (`X`: exterior,
data-front, endpoint) is unchanged. Applying `histogram_update` in every invocation lowers
the total mass by exactly `L = v_b ℓ_a + v_a ℓ_b`. So if the old mass is `Wm - N + 2L`, the
new mass is `s = Wm - N + L` and `Wm - s = N - L`. -/
theorem copied_mass (Ha Hb : ℕ → ℤ) (ha hb n : ℕ) (ha1 : 1 < ha) (hb1 : 1 < hb)
    (han : ha < n) (hbn : hb < n) (va vb X W m N : ℤ)
    (hold : X + vb * ∑ r ∈ range n, (r : ℤ) * Ha r + va * ∑ r ∈ range n, (r : ℤ) * Hb r =
      W * m - N + 2 * (vb * (ha * (ha - 1)) + va * (hb * (hb - 1)))) :
    let s := X + vb * ∑ r ∈ range n, (r : ℤ) * updated Ha ha r +
      va * ∑ r ∈ range n, (r : ℤ) * updated Hb hb r
    let L := vb * (ha * (ha - 1)) + va * (hb * (hb - 1))
    s = W * m - N + L ∧ W * m - s = N - L := by
  intro s L
  have ea := histogram_update Ha ha n ha1 han
  have eb := histogram_update Hb hb n hb1 hbn
  have hs : s = X + vb * (∑ r ∈ range n, (r : ℤ) * Ha r - ha * (ha - 1)) +
      va * (∑ r ∈ range n, (r : ℤ) * Hb r - hb * (hb - 1)) := by
    simp only [s, updated, ea, eb]
  constructor <;> rw [hs] <;> linarith

/-- the selected `(23, 25)` network (`docs/research/community-round2-review.md`):
`N = 4073300`, `W = 2N + v₂₅·27918 + v₂₃·36586 = 137151806`, `L = 2226400`,
`Wm - s = 1846900` and `s = 78860441550` -/
theorem selected_network :
    let va : ℤ := (Nat.choose 23 3 : ℕ)
    let vb : ℤ := (Nat.choose 25 3 : ℕ)
    let N := va * vb
    let W := 2 * N + vb * 27918 + va * 36586
    let L := vb * (23 * 22) + va * (25 * 24)
    N = 4073300 ∧ W = 137151806 ∧ L = 2226400 ∧ N - L = 1846900 ∧
      W * 575 - N + L = 78860441550 := by
  intro va vb N W L
  simp only [N, W, L, va, vb]
  norm_num [Nat.choose]

/-- Swapnil's direct centres (round six, `h = 25`): `L = 2 v h c₀` with `c₀ = h`, and the
deficit `N - L = v(v - 2h²) = 2415000` -/
theorem direct_deficit :
    let v : ℤ := (Nat.choose 25 3 : ℕ)
    v * v - 2 * v * 25 * 25 = v * (v - 2 * 25 ^ 2) ∧ v * v - 2 * v * 25 * 25 = 2415000 := by
  intro v
  simp only [v]
  norm_num [Nat.choose]

/-- Swapnil's retained point totals (round six, `h = 23`): loss `h - 1` per centre, so
`L = 2 v h (h - 1)` and `N - L = 1344189`, the deficit of `lean/Round6.lean`'s bit
histogram (`148225616 · 529 - 78410006675`) -/
theorem retained_totals_deficit :
    let v : ℤ := (Nat.choose 23 3 : ℕ)
    v * v - 2 * v * 23 * 22 = 1344189 ∧ (148225616 : ℤ) * 529 - 78410006675 = 1344189 := by
  intro v
  simp only [v]
  norm_num [Nat.choose]

end Mass

end KappaCheck.CopiedCentres
