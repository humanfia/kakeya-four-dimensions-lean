import Submission.Obl.k4_scalar_guarded_entropic_path.Info.MeasureScore
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.Canonical
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.InformationExponent

/-!
# Choosing the information window

`exists_window_info`: a family of measured windows on one common finite law `P` (each
window parent `a` reads a common point `ω` as the incidence `π a ω`, and its world label is a
function `wm a` of one top world label, nested along the windows) has a window `a < L` whose
frozen information expression `∑ ω_i * rlScore (σ_i) canonX canonY canonZ` is at most half its
weighted mass times `log (N ^ α)`, `α = informationExponent N (windowCost L C M Kv Ks)`, for
any world laws `σ_i` that are, up to the weights and one factor, the world slices of `P`.

The common atoms are the top world, the canonical codes read in every window, and the
common velocity record; the choice is x0567's `exists_low_information_readout_window`
(StateReadout, built on accepted o038), transferred by `weighted_rlScore_eq`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open Submission.Obl.k4_matching_palette_likelihood
open scoped ENNReal

noncomputable section

variable {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T]

/-- Positive atoms satisfy every almost-sure property of the code. -/
theorem codeProb_pos_mem (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    {Q : T → Prop} (hQ : ∀ᵐ ω ∂P, Q (Φ ω)) {t : T} (ht : 0 < codeProb P Φ t) : Q t := by
  by_contra hq
  have hzero : P {ω | Φ ω = t} = 0 := by
    apply measure_mono_null _ (ae_iff.mp hQ)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω]; exact hq
  have : codeProb P Φ t = 0 := by simp [codeProb, codeLaw, hzero]
  linarith

/-- An almost-sure finite range bounds the number of values on positive atoms. -/
theorem card_image_pos_le (P : Measure Ω) [IsFiniteMeasure P] {Φ : Ω → T}
    {β : Type*} [DecidableEq β] (G : T → β) (H : T → Prop) [DecidablePred H] (S : Finset β)
    (hS : ∀ᵐ ω ∂P, H (Φ ω) → G (Φ ω) ∈ S) :
    ((Finset.univ.filter (fun y => 0 < codeProb P Φ y ∧ H y)).image G).card ≤ S.card := by
  classical
  apply Finset.card_le_card
  intro b hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hy' := (Finset.mem_filter.mp hy).2
  exact codeProb_pos_mem (Q := fun t => H t → G t ∈ S) P hS hy'.1 hy'.2

theorem sum_tagSlice_univ (P : Measure Ω) {W : ℕ} {π : Ω → Fin W × Incidence}
    (hπ : Measurable π) : (∑ i, tagSlice P π i Set.univ) = P Set.univ := by
  classical
  have hπ1 : Measurable (fun ω => (π ω).1) := measurable_fst.comp hπ
  have hπ2 : Measurable (fun ω => (π ω).2) := measurable_snd.comp hπ
  simp only [tagSlice, Measure.map_apply hπ2 MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]
  rw [← measure_biUnion_finset]
  · congr 1; ext ω; simp
  · intro i _ j _ hij
    exact Set.disjoint_left.mpr fun ω h h' => hij (h.symm.trans h')
  · intro i _
    exact hπ1 (measurableSet_singleton i)


/-- The information cost of the chosen window. -/
def windowCost (L C M Kv Ks : ℕ) : ℝ :=
  (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + Real.log (Kv : ℝ) + Real.log (Ks : ℝ) + 4

theorem windowCost_nonneg {L C M Kv Ks : ℕ} (hM : 1 ≤ M) (hKv : 1 ≤ Kv) (hKs : 1 ≤ Ks) :
    0 ≤ windowCost L C M Kv Ks := by
  unfold windowCost
  have h1 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have h2 : 0 ≤ Real.log (Kv : ℝ) := Real.log_nonneg (by exact_mod_cast hKv)
  have h3 : 0 ≤ Real.log (Ks : ℝ) := Real.log_nonneg (by exact_mod_cast hKs)
  have h4 : 0 ≤ (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) := by positivity
  linarith

/-- Index of a value in a finite set, with one outside index. -/
def setIndex (S : Finset ℤ) (z : ℤ) : Fin (S.card + 1) := by
  classical
  exact if h : z ∈ S then Fin.castSucc (S.equivFin ⟨z, h⟩) else Fin.last _

theorem setIndex_lt {S : Finset ℤ} {z : ℤ} (hz : z ∈ S) : ((setIndex S z : ℕ)) < S.card := by
  classical
  simp [setIndex, hz]

theorem setIndex_injOn {S : Finset ℤ} {z z' : ℤ} (hz : z ∈ S) (hz' : z' ∈ S)
    (h : setIndex S z = setIndex S z') : z = z' := by
  classical
  simp only [setIndex, hz, hz', dite_true] at h
  have := S.equivFin.injective (Fin.castSucc_injective _ h)
  simpa using congrArg Subtype.val this


/-- The common atoms of a family of measured windows: the top world, the canonical codes
of the incidence read in every window, and the index of the common velocity record. -/
abbrev WindowAtom (Wt L C : ℕ) (m : ℕ) (Mb : ℤ) (Sv : Finset ℤ) : Type :=
  Fin Wt × (Fin (L + C) → Fin (canonN m Mb)) × Fin (Sv.card + 1)


/-- The common atom code. -/
def windowAtom {Wt L C : ℕ} (top : Ω → Fin Wt) {w : ℕ → ℕ}
    (π : (a : ℕ) → Ω → Fin (w a) × Incidence) (N : ℝ) (m : ℕ) (Mb : ℤ)
    (vel : Ω → ℤ) (Sv : Finset ℤ) (ω : Ω) : WindowAtom Wt L C m Mb Sv :=
  (top ω, fun a => canonX N m Mb (π a ω).2, setIndex Sv (vel ω))

theorem measurable_windowAtom {Wt L C : ℕ} {top : Ω → Fin Wt} (htop : Measurable top)
    {w : ℕ → ℕ} {π : (a : ℕ) → Ω → Fin (w a) × Incidence} (hπ : ∀ a, Measurable (π a))
    (N : ℝ) (m : ℕ) (Mb : ℤ) {vel : Ω → ℤ} (hvel : Measurable vel) (Sv : Finset ℤ) :
    Measurable (windowAtom (L := L) (C := C) top π N m Mb vel Sv) := by
  refine htop.prodMk (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.mpr fun a =>
      (measurable_canonX N m Mb).comp (measurable_snd.comp (hπ a))
  · exact (measurable_of_countable (setIndex Sv)).comp hvel



theorem codeProb_nonneg (P : Measure Ω) {T : Type*} (Φ : Ω → T) (t : T) :
    0 ≤ codeProb P Φ t :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem sum_codeProb (P : Measure Ω) [IsFiniteMeasure P] {T : Type*} [Fintype T]
    [MeasurableSpace T] [MeasurableSingletonClass T] {Φ : Ω → T} (hΦ : Measurable Φ)
    (hP : P Set.univ ≠ 0) : ∑ t, codeProb P Φ t = 1 := by
  unfold codeProb
  rw [← Finset.sum_div, sum_codeLaw P hΦ]
  exact div_self (ENNReal.toReal_ne_zero.mpr ⟨hP, measure_ne_top _ _⟩)

/-- The total weighted mass of a window whose world laws are slices of `c • P`. -/
theorem window_mass_eq (P : Measure Ω) [IsFiniteMeasure P] {W : ℕ}
    {π : Ω → Fin W × Incidence} (hπ : Measurable π) (wt : Fin W → ℝ) {c : ℝ}
    (σ : Fin W → Measure Incidence)
    (hσ : ∀ i, ENNReal.ofReal (wt i) • σ i = ENNReal.ofReal c • tagSlice P π i) :
    (∑ i, ENNReal.ofReal (wt i) * σ i Set.univ) = ENNReal.ofReal c * P Set.univ := by
  calc (∑ i, ENNReal.ofReal (wt i) * σ i Set.univ)
      = ∑ i, ENNReal.ofReal c * tagSlice P π i Set.univ := by
        apply Finset.sum_congr rfl
        intro i _
        have := congrArg (fun μ : Measure Incidence => μ Set.univ) (hσ i)
        simpa only [Measure.smul_apply, smul_eq_mul] using this
    _ = ENNReal.ofReal c * P Set.univ := by
        rw [← Finset.mul_sum, sum_tagSlice_univ P hπ]



/-- **The information window.** A family of measured windows on one common finite law
`P` (`π a` reads each common point as an incidence of window parent `a`, with world
labels nested along the windows) has a window `a < L` whose frozen information expression,
for the canonical code and any world laws that are (up to weights and one factor) the world
slices of `P`, is at most half the weighted mass times `log (N ^ α)` with
`α = informationExponent N (windowCost L C M Kv Ks)`. Here `M` bounds the common velocity
records, `Kv` the window velocity bins given a world and a common velocity record, and `Ks`
the window grid records given the world `C` windows later. -/
theorem exists_window_info (P : Measure Ω) [IsFiniteMeasure P] {L C : ℕ} (hL : 0 < L)
    (hC : 1 ≤ C) {Wt : ℕ} {top : Ω → Fin Wt} (htop : Measurable top)
    {w : ℕ → ℕ} (wm : (a : ℕ) → Fin Wt → Fin (w a))
    (hnest : ∀ a, a + 1 ≤ L + C → ∀ x y, wm (a + 1) x = wm (a + 1) y → wm a x = wm a y)
    (π : (a : ℕ) → Ω → Fin (w a) × Incidence) (hπ : ∀ a, Measurable (π a))
    (hπw : ∀ a, ∀ᵐ ω ∂P, (π a ω).1 = wm a (top ω))
    {N : ℝ} (hN : 2 ≤ N) (m : ℕ) (Mb : ℤ)
    {vel : Ω → ℤ} (hvel : Measurable vel) (Sv : Finset ℤ) (hSv : ∀ᵐ ω ∂P, vel ω ∈ Sv)
    {Kv Ks : ℕ} (hKv : 1 ≤ Kv) (hKs : 1 ≤ Ks)
    (hv : ∀ a < L, ∀ (j : Fin (w a)) (z₀ : ℤ), ∃ S : Finset ℤ, S.card ≤ Kv ∧
      ∀ᵐ ω ∂P, wm a (top ω) = j → vel ω = z₀ → canonZ m Mb (canonX N m Mb (π a ω).2) ∈ S)
    (hs : ∀ a < L, ∀ j : Fin (w (a + C)), ∃ S : Finset ℕ, S.card ≤ Ks ∧
      ∀ᵐ ω ∂P, wm (a + C) (top ω) = j → canonY m Mb (canonX N m Mb (π a ω).2) ∈ S) :
    ∃ a < L, ∀ (wt : Fin (w a) → ℝ), (∀ i, 0 ≤ wt i) → ∀ (c : ℝ), 0 ≤ c →
      ∀ (σ : Fin (w a) → Measure Incidence), (∀ i, IsFiniteMeasure (σ i)) →
      (∀ i, ENNReal.ofReal (wt i) • σ i = ENNReal.ofReal c • tagSlice P (π a) i) →
      (∑ i, wt i * rlScore (σ i) (canonX N m Mb) (canonY m Mb) (canonZ m Mb)) ≤
        ((∑ i, ENNReal.ofReal (wt i) * σ i Set.univ).toReal / 2) *
          Real.log (N ^ informationExponent N (windowCost L C (max Sv.card 1) Kv Ks)) := by
  classical
  set T := WindowAtom Wt L C m Mb Sv
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let Φ : Ω → T := windowAtom top π N m Mb vel Sv
  have hΦ : Measurable Φ := measurable_windowAtom htop hπ N m Mb hvel Sv
  let Φ' : Ω → Fin (Fintype.card T) := fun ω => e (Φ ω)
  have hΦ' : Measurable Φ' := (measurable_of_countable e).comp hΦ
  have heΦ : ∀ ω, e.symm (Φ' ω) = Φ ω := fun ω => e.symm_apply_apply _
  set p := codeProb P Φ'
  -- the window score on the common atoms, for any chosen window
  have htransfer : ∀ a (ha : a < L + C) (wt : Fin (w a) → ℝ), (∀ i, 0 ≤ wt i) →
      ∀ (c : ℝ), 0 ≤ c → ∀ (σ : Fin (w a) → Measure Incidence), (∀ i, IsFiniteMeasure (σ i)) →
      (∀ i, ENNReal.ofReal (wt i) • σ i = ENNReal.ofReal c • tagSlice P (π a) i) →
      (∑ i, wt i * rlScore (σ i) (canonX N m Mb) (canonY m Mb) (canonZ m Mb)) =
        c * ((P Set.univ).toReal * positiveScore p (fun t => (wm a (e.symm t).1).val)
          (pairedRecord (fun t => (wm a (e.symm t).1).val)
            (canonY m Mb ∘ fun t => (e.symm t).2.1 ⟨a, ha⟩))
          ((zEnc ∘ canonZ m Mb) ∘ fun t => (e.symm t).2.1 ⟨a, ha⟩)) := by
    intro a ha wt hwt c hc σ hσfin hσ
    have := weighted_rlScore_eq (Φ := Φ') (f := fun t => wm a (e.symm t).1)
      (φ := fun t => (e.symm t).2.1 ⟨a, ha⟩) P hΦ' (hπ a)
      (by filter_upwards [hπw a] with ω hω; rw [heΦ]; exact hω)
      (measurable_canonX N m Mb) (Filter.Eventually.of_forall fun ω => by rw [heΦ]; rfl)
      (canonY m Mb) (canonZ m Mb) wt hwt hc σ hσ
    exact this
  -- the budget inequality from a score bound
  have hbudget : ∀ a (ha : a < L + C) (score : ℝ),
      score ≤ windowCost L C (max Sv.card 1) Kv Ks →
      score = positiveScore p (fun t => (wm a (e.symm t).1).val)
          (pairedRecord (fun t => (wm a (e.symm t).1).val)
            (canonY m Mb ∘ fun t => (e.symm t).2.1 ⟨a, ha⟩))
          ((zEnc ∘ canonZ m Mb) ∘ fun t => (e.symm t).2.1 ⟨a, ha⟩) →
      ∀ (wt : Fin (w a) → ℝ), (∀ i, 0 ≤ wt i) → ∀ (c : ℝ), 0 ≤ c →
      ∀ (σ : Fin (w a) → Measure Incidence), (∀ i, IsFiniteMeasure (σ i)) →
      (∀ i, ENNReal.ofReal (wt i) • σ i = ENNReal.ofReal c • tagSlice P (π a) i) →
      (∑ i, wt i * rlScore (σ i) (canonX N m Mb) (canonY m Mb) (canonZ m Mb)) ≤
        ((∑ i, ENNReal.ofReal (wt i) * σ i Set.univ).toReal / 2) *
          Real.log (N ^ informationExponent N (windowCost L C (max Sv.card 1) Kv Ks)) := by
    intro a ha score hscore hdef wt hwt c hc σ hσfin hσ
    rw [htransfer a ha wt hwt c hc σ hσfin hσ, ← hdef,
      window_mass_eq P (hπ a) wt σ hσ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    have hT := windowCost_nonneg (L := L) (C := C) (le_max_right Sv.card 1) hKv hKs
    apply informationExponent_weighted_budget hN hT
      (mul_nonneg hc ENNReal.toReal_nonneg)
    calc c * ((P Set.univ).toReal * score) = (c * (P Set.univ).toReal) * score := by ring
      _ ≤ (c * (P Set.univ).toReal) * windowCost L C (max Sv.card 1) Kv Ks :=
        mul_le_mul_of_nonneg_left hscore (mul_nonneg hc ENNReal.toReal_nonneg)
  have hp0 : ∀ t, 0 ≤ p t := fun t => codeProb_nonneg P Φ' t
  by_cases hP : P Set.univ = 0
  · -- the zero law: every score vanishes
    refine ⟨0, hL, hbudget 0 (by omega) _ ?_ rfl⟩
    have hpz : ∀ t, p t = 0 := by
      intro t
      simp [p, codeProb, hP]
    unfold positiveScore
    simp only [hpz, zero_mul, Finset.sum_const_zero]
    exact windowCost_nonneg (le_max_right Sv.card 1) hKv hKs
  -- the finite records on the common atoms
  let F : ℕ → Fin (Fintype.card T) → ℕ := fun a t =>
    if a ≤ L + C then (wm a (e.symm t).1).val else (wm (L + C) (e.symm t).1).val
  let Z : Fin (Fintype.card T) → ℕ := fun t => ((e.symm t).2.2 : ℕ)
  let V : ℕ → Fin (Fintype.card T) → ℕ := fun a t =>
    if h : a < L + C then zEnc (canonZ m Mb ((e.symm t).2.1 ⟨a, h⟩)) else 0
  let Y : ℕ → Fin (Fintype.card T) → ℕ := fun a t =>
    if h : a < L + C then canonY m Mb ((e.symm t).2.1 ⟨a, h⟩) else 0
  have hp1 : ∑ t, p t = 1 := sum_codeProb P hΦ' hP
  have hnestF : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y := by
    intro k x y h
    by_cases hk : k + 1 ≤ L + C
    · have hk' : k ≤ L + C := by omega
      simp only [F, hk, hk', if_true] at h ⊢
      exact congrArg Fin.val (hnest k hk _ _ (Fin.ext h))
    · by_cases hk2 : k ≤ L + C
      · have hkeq : k = L + C := by omega
        subst hkeq
        simp only [F, hk, le_refl, if_true, if_false] at h ⊢
        exact h
      · have hk3 : ¬ (k + 1 ≤ L + C) := hk
        simp only [F, hk3, hk2, if_false] at h ⊢
        exact h
  have hsupp' : ∀ x, ((Finset.univ.filter (fun y =>
      0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ max Sv.card 1 := by
    intro x
    refine le_trans (card_image_pos_le (Φ := Φ') P Z (fun y => F 0 y = F 0 x)
      (Finset.range Sv.card) ?_) (by simp)
    filter_upwards [hSv] with ω hω _
    simp only [Z, heΦ, Φ, windowAtom, Finset.mem_range]
    exact setIndex_lt hω
  have hv' : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      pairedRecord (F a) Z y = pairedRecord (F a) Z x)).image (V a)).card ≤ Kv := by
    intro a ha x
    have haLC : a ≤ L + C := by omega
    have haLT : a < L + C := by omega
    by_cases hin : ((e.symm x).2.2 : ℕ) < Sv.card
    · let z₀ : ℤ := (Sv.equivFin.symm ⟨(e.symm x).2.2, hin⟩).val
      have hz₀ : z₀ ∈ Sv := (Sv.equivFin.symm ⟨(e.symm x).2.2, hin⟩).2
      have hidx₀ : setIndex Sv z₀ = (e.symm x).2.2 := by
        apply Fin.ext
        simp [setIndex, hz₀, z₀]
      obtain ⟨S, hScard, hSae⟩ := hv a ha (wm a (e.symm x).1) z₀
      refine le_trans (card_image_pos_le (Φ := Φ') P (V a) _ (S.image zEnc) ?_)
        (Finset.card_image_le.trans hScard)
      filter_upwards [hSv, hSae] with ω hω hS hpair
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp hpair
      have hw : wm a (top ω) = wm a (e.symm x).1 := by
        apply Fin.ext
        simpa only [F, haLC, if_true, heΦ, Φ, windowAtom] using h1
      have hz : vel ω = z₀ := by
        have hidx : setIndex Sv (vel ω) = (e.symm x).2.2 := by
          apply Fin.ext
          simpa only [Z, heΦ, Φ, windowAtom] using h2
        exact setIndex_injOn hω hz₀ (hidx.trans hidx₀.symm)
      have hmem := hS hw hz
      simp only [V, haLT, dite_true, heΦ, Φ, windowAtom, Finset.mem_image]
      exact ⟨_, hmem, rfl⟩
    · refine le_trans (card_image_pos_le (Φ := Φ') P (V a) _ ∅ ?_) (by simp)
      filter_upwards [hSv] with ω hω hpair
      exfalso
      obtain ⟨_, h2⟩ := Nat.pair_eq_pair.mp hpair
      have hlt := setIndex_lt hω
      have : ((setIndex Sv (vel ω) : Fin (Sv.card + 1)) : ℕ) = ((e.symm x).2.2 : ℕ) := by
        simpa only [Z, heΦ, Φ, windowAtom] using h2
      omega
  have hs' : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      F (a + C) y = F (a + C) x)).image (Y a)).card ≤ Ks := by
    intro a ha x
    have haLC : a + C ≤ L + C := by omega
    have haLT : a < L + C := by omega
    obtain ⟨S, hScard, hSae⟩ := hs a ha (wm (a + C) (e.symm x).1)
    refine le_trans (card_image_pos_le (Φ := Φ') P (Y a) _ S ?_) hScard
    filter_upwards [hSae] with ω hS hF
    have hw : wm (a + C) (top ω) = wm (a + C) (e.symm x).1 := by
      apply Fin.ext
      simpa only [F, haLC, if_true, heΦ, Φ, windowAtom] using hF
    simpa only [Y, haLT, dite_true, heΦ, Φ, windowAtom] using hS hw
  have hY' : ∀ a < L, ∀ x y, pairedRecord (F (a + C)) (Y a) x =
      pairedRecord (F (a + C)) (Y a) y → Y a x = Y a y :=
    fun a _ x y h => (Nat.pair_eq_pair.mp h).2
  obtain ⟨a, ha, hsc⟩ := exists_low_information_readout_window (Fintype.card T) L C
    (max Sv.card 1) Kv Ks p F Z V Y Y hL hC (le_max_right _ _) hKv hKs hp0 hp1 hnestF
    hsupp' hv' hs' hY'
  have haLC : a ≤ L + C := by omega
  have haLT : a < L + C := by omega
  have hFa : F a = fun t => (wm a (e.symm t).1).val := by
    funext t; simp only [F, haLC, if_true]
  have hYa : Y a = canonY m Mb ∘ fun t => (e.symm t).2.1 ⟨a, haLT⟩ := by
    funext t; simp only [Y, haLT, dite_true, Function.comp_apply]
  have hVa : V a = (zEnc ∘ canonZ m Mb) ∘ fun t => (e.symm t).2.1 ⟨a, haLT⟩ := by
    funext t; simp only [V, haLT, dite_true, Function.comp_apply]
  refine ⟨a, ha, hbudget a haLT _ ?_ rfl⟩
  rw [← hFa, ← hYa, ← hVa]
  exact hsc

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open Submission.Obl.k4_matching_palette_likelihood
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The information window, in bin form.** As `exists_window_info`, with the window
incidences bounded almost surely (time in `[0, 1]`, coefficients at most `K`), and the two
ambiguity hypotheses stated for the raw bins: the window velocity bin at resolution `m`
given the window world and the common velocity record, and the window grid part (all
base and hidden bins at the tangent resolutions `j / m`) given the world `C` windows
later. The canonical code is the one of the box `canonM N K m`. -/
theorem exists_window_info_bins (P : Measure Ω) [IsFiniteMeasure P] {L C : ℕ}
    (hL : 0 < L) (hC : 1 ≤ C) {Wt : ℕ} {top : Ω → Fin Wt} (htop : Measurable top)
    {w : ℕ → ℕ} (wm : (a : ℕ) → Fin Wt → Fin (w a))
    (hnest : ∀ a, a + 1 ≤ L + C → ∀ x y, wm (a + 1) x = wm (a + 1) y → wm a x = wm a y)
    (π : (a : ℕ) → Ω → Fin (w a) × Incidence) (hπ : ∀ a, Measurable (π a))
    (hπw : ∀ a, ∀ᵐ ω ∂P, (π a ω).1 = wm a (top ω))
    {N K : ℝ} (hN : 2 ≤ N) (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    (hbound : ∀ a < L, ∀ᵐ ω ∂P, (π a ω).2.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ e, |(π a ω).2.1.2 e| ≤ K)
    {vel : Ω → ℤ} (hvel : Measurable vel) (Sv : Finset ℤ) (hSv : ∀ᵐ ω ∂P, vel ω ∈ Sv)
    {Kv Ks : ℕ} (hKv : 1 ≤ Kv) (hKs : 1 ≤ Ks)
    (hv : ∀ a < L, ∀ (j : Fin (w a)) (z₀ : ℤ), ∃ S : Finset ℤ, S.card ≤ Kv ∧
      ∀ᵐ ω ∂P, wm a (top ω) = j → vel ω = z₀ → velocityBin N (m : ℝ) ((π a ω).2.1.2 1) ∈ S)
    (hs : ∀ a < L, ∀ j : Fin (w (a + C)), ∃ S : Finset (GridPart m), S.card ≤ Ks ∧
      ∀ᵐ ω ∂P, wm (a + C) (top ω) = j → gridPart N m (π a ω).2 ∈ S) :
    ∃ a < L, ∀ (wt : Fin (w a) → ℝ), (∀ i, 0 ≤ wt i) → ∀ (c : ℝ), 0 ≤ c →
      ∀ (σ : Fin (w a) → Measure Incidence), (∀ i, IsFiniteMeasure (σ i)) →
      (∀ i, ENNReal.ofReal (wt i) • σ i = ENNReal.ofReal c • tagSlice P (π a) i) →
      (∑ i, wt i * rlScore (σ i) (canonX N m (canonM N K m)) (canonY m (canonM N K m))
          (canonZ m (canonM N K m))) ≤
        ((∑ i, ENNReal.ofReal (wt i) * σ i Set.univ).toReal / 2) *
          Real.log (N ^ informationExponent N (windowCost L C (max Sv.card 1) Kv Ks)) := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by linarith
  apply exists_window_info P hL hC htop wm hnest π hπ hπw hN m (canonM N K m) hvel Sv hSv
    hKv hKs
  · intro a ha j z₀
    obtain ⟨S, hS, hae⟩ := hv a ha j z₀
    refine ⟨S, hS, ?_⟩
    filter_upwards [hae, hbound a ha] with ω h hb hw hz
    have hmem := gridTuple_mem_boxSet hN1 hK hm hb.1 hb.2
    rw [canonZ_canonX hmem]
    exact h hw hz
  · intro a ha j
    obtain ⟨S, hS, hae⟩ := hs a ha j
    refine ⟨S.image (gridEnc m), Finset.card_image_le.trans hS, ?_⟩
    filter_upwards [hae, hbound a ha] with ω h hb hw
    have hmem := gridTuple_mem_boxSet hN1 hK hm hb.1 hb.2
    rw [canonY_canonX hmem]
    exact Finset.mem_image_of_mem _ (h hw)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
