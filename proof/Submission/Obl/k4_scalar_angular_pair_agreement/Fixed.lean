import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.Defs
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic
import Submission.Obl.k4_scalar_angular_pair_agreement.Extrap
import Submission.Obl.k4_scalar_angular_pair_agreement.AllPairs
import Submission.Obl.k4_scalar_angular_pair_agreement.BadPairs
import Submission.Obl.k4_scalar_angular_pair_agreement.CapIntegration

/-!
# The fixed-scale pair estimate

At one scale `k`, for a true terminal chart system and a coarsened depth `T₁ ≤ T`, the
weighted mass of all same-world same-coarse-block pairs is at most the good-pair mass plus
the bad-pair mass.  A bad pair `(i, i')` (no whole-box agreement) has its common
trajectories in boundedly many angular bins; through the original joint
terminal/angular law this bounds the bad-pair mass by the cap exceptional mass plus an
explicit power of `N`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

section Blocks

open scoped Classical

/-- Labels of world `w` whose fine block lies in the coarse block `b`. -/
noncomputable def Sblk (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => γ i = w ∧ I T (j i) ⊆ I T₁ b)

/-- Selected incidences of world `w` in the coarse block `b`. -/
def Dblk (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (T₁ : ℕ) (w : Fin (W p k))
    (b : Fin (2 ^ T₁)) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  ⋃ i ∈ Sblk p k T n γ j T₁ w b, C i

/-- Witness incidences in the coarse block `b` whose labels are bad for the source `i`. -/
noncomputable def Gwit (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k))
    (b : Fin (2 ^ T₁)) (i : Fin n) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  ⋃ i' ∈ (Sblk p k T n γ j T₁ w b).filter (fun i' => ¬ Agrees p k T₁ n u v P a e b i i'), C i'

lemma mem_Sblk {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {T₁ : ℕ} {w : Fin (W p k)} {b : Fin (2 ^ T₁)} {i : Fin n} :
    i ∈ Sblk p k T n γ j T₁ w b ↔ γ i = w ∧ I T (j i) ⊆ I T₁ b := by
  simp [Sblk]

lemma measurableSet_Dblk {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    (hC : ∀ i, MeasurableSet (C i)) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁)) :
    MeasurableSet (Dblk p k T n γ j C T₁ w b) :=
  Finset.measurableSet_biUnion _ (fun i _ => hC i)

lemma measurableSet_Gwit {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    (hC : ∀ i, MeasurableSet (C i)) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁)) (i : Fin n) :
    MeasurableSet (Gwit p k T n γ j C u v P a e T₁ w b i) :=
  Finset.measurableSet_biUnion _ (fun i _ => hC i)

/-- Every same-block pair is good or has a bad source/witness label pair. -/
lemma pairSet_Dblk_subset {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    (hCsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k))
    (b : Fin (2 ^ T₁)) :
    pairSet (Dblk p k T n γ j C T₁ w b) (Dblk p k T n γ j C T₁ w b) ⊆
      goodPairs p k T n γ j C u v P a e T₁ w b ∪
        ⋃ i ∈ Sblk p k T n γ j T₁ w b, pairSet (C i) (Gwit p k T n γ j C u v P a e T₁ w b i) := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  simp only [Dblk, mem_iUnion] at h1 h2
  obtain ⟨i, hi, hzi⟩ := h1
  obtain ⟨i', hi', hzi'⟩ := h2
  have hi0 := mem_Sblk.mp hi
  have hi0' := mem_Sblk.mp hi'
  by_cases hag : Agrees p k T₁ n u v P a e b i i'
  · left
    refine ⟨hi0.2 ((hCsub i hzi).2).2, hi0'.2 ((hCsub i' hzi').2).2, i, i', hi0.1, hi0'.1,
      hi0.2, hi0'.2, hzi, hzi', hag⟩
  · right
    simp only [mem_iUnion]
    refine ⟨i, hi, hzi, ?_⟩
    simp only [Gwit, mem_iUnion]
    exact ⟨i', Finset.mem_filter.mpr ⟨hi', hag⟩, hzi'⟩

/-- Summing over the coarse blocks of a world is summing over the labels of the world. -/
lemma sum_Sblk {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {T₁ : ℕ} (hT₁ : T₁ ≤ T) (w : Fin (W p k)) (g : Fin n → ℝ≥0∞) :
    ∑ b : Fin (2 ^ T₁), ∑ i ∈ Sblk p k T n γ j T₁ w b, g i =
      ∑ i ∈ Finset.univ.filter (fun i => γ i = w), g i := by
  simp only [Sblk, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hγ : γ i = w
  · simp only [hγ, true_and, ite_true]
    obtain ⟨b₀, hb₀⟩ := exists_coarse hT₁ (j i)
    rw [Finset.sum_eq_single b₀]
    · simp [hb₀]
    · intro b _ hb
      have : ¬ I T (j i) ⊆ I T₁ b := fun h => hb (coarse_unique hT₁ (j i) h hb₀)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ b₀) h
  · simp [hγ]

/-- Per coarse block: the all-pairs measure is at most the good-pair measure plus, for each
source label, `2⁻ᵀ` times the measure of its bad witnesses over its assignment. -/
lemma pair_decomp {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hA : ∀ i, MeasurableSet (A i))
    (hC : ∀ i, MeasurableSet (C i))
    (hCsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k))
    (b : Fin (2 ^ T₁)) (ν₀ : Measure (ℕ × (Fin 5 → ℝ))) [SFinite ν₀] :
    (ν₀.prod (volume.prod volume))
        (pairSet (Dblk p k T n γ j C T₁ w b) (Dblk p k T n γ j C T₁ w b)) ≤
      (ν₀.prod (volume.prod volume)) (goodPairs p k T n γ j C u v P a e T₁ w b) +
        ∑ i ∈ Sblk p k T n γ j T₁ w b, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
          (ν₀.prod volume) (Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) := by
  refine (measure_mono (pairSet_Dblk_subset hCsub u v P a e T₁ w b)).trans ?_
  refine (measure_union_le _ _).trans ?_
  gcongr
  refine (measure_biUnion_finset_le _ _).trans ?_
  gcongr with i _
  refine pairSet_le_witness ν₀ (hC i) (measurableSet_Gwit hC u v P a e T₁ w b i) (hA i)
    (Js := I T (j i)) (fun z hz => (hCsub i hz).2) ?_
  rw [volume_I]

end Blocks

/-- The joint terminal/angular observation of an incidence. -/
noncomputable def obsA (p : Code) (k : ℕ) (uu : ℝ) (q : (ℕ × (Fin 5 → ℝ)) × ℝ) :
    ((Fin 2 → ℝ) × ℤ) × ℤ :=
  (((![q.2, y q.1 q.2] : Fin 2 → ℝ), (⌊x q.1 q.2 / (N p k ^ (-(L p)))⌋ : ℤ)),
    (⌊q.1.2 1 / (N p k ^ (-uu))⌋ : ℤ))

lemma measurable_obsA (p : Code) (k : ℕ) (uu : ℝ) : Measurable (obsA p k uu) :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsG _ _

/-- The exceptional set of the joint terminal/angular cap. -/
def Exc (p : Code) (k : ℕ) (w : Fin (W p k)) (uu τ : ℝ) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  {q | ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ)) < G p k w uu (obsA p k uu q)}

lemma measurableSet_Exc (p : Code) (k : ℕ) (w : Fin (W p k)) (uu τ : ℝ)
    (hG : Measurable (G p k w uu)) : MeasurableSet (Exc p k w uu τ) :=
  measurableSet_lt measurable_const (hG.comp (measurable_obsA p k uu))

section Cap

open scoped Classical

set_option maxHeartbeats 400000 in
/-- Bad witnesses of a source label, outside the cap exceptional set, are charged to the
reference measure of a strip times a hidden-bin range times boundedly many angular bins
per listed witness label. -/
lemma witness_cap_bound {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)} {ε : ℝ}
    (hNpos : 0 < N p k)
    (hA : ∀ i, MeasurableSet (A i)) (hC : ∀ i, MeasurableSet (C i))
    (hCsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i)))
    (hfit : ∀ i, ∀ l ∈ A i, ∀ t ∈ I T (j i), |y l t - u i - t * v i| ≤ N p k ^ ε * J i ∧
        |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N p k ^ ε * N p k ^ (-(L p)))
    (hJ : ∀ i, 0 < J i)
    (hdeg : ∀ i, (P i).totalDegree ≤ 2)
    (hΛcard : ∀ a z, ((Λ a z).card : ℝ) ≤ N p k ^ ε)
    (hΛmeas : ∀ a i, MeasurableSet {z | i ∈ Λ a z})
    (hΛae : ∀ i, mu p k (γ i) {q | q ∈ C i ∧ i ∉ Λ (γ i) ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
        (⌊x q.1 q.2 / (N p k ^ (-(L p)))⌋ : ℤ))} = 0)
    {uu τ : ℝ} (w : Fin (W p k)) (hGmeas : Measurable (G p k w uu))
    (hmap : Measure.map (obsA p k uu) (mu p k w) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (G p k w uu))
    {a e : ℝ} {T₁ : ℕ} (hT₁ : T₁ ≤ T)
    (Fb : Fin (2 ^ T₁) → Fin n → Fin n → Finset ℤ)
    (hFb : ∀ b i i', i ∈ Sblk p k T n γ j T₁ w b → i' ∈ Sblk p k T n γ j T₁ w b →
      ¬ Agrees p k T₁ n u v P a e b i i' →
      (Fb b i i').card ≤ 6 ∧ ∀ l ∈ A i ∩ A i', ⌊l.2 1 / N p k ^ (-uu)⌋ ∈ Fb b i i')
    (b : Fin (2 ^ T₁)) (i : Fin n) (hi : i ∈ Sblk p k T n γ j T₁ w b) :
    ((ν p k w).prod volume) (Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ≤
      mu p k w ((Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ∩ Exc p k w uu τ) +
      ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ)) *
        (ENNReal.ofReal (2 * (48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * N p k ^ ε + 1) + 1) *
          (ENNReal.ofReal (N p k ^ ε) * 6) *
          ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹ *
            (2 * ((1 + 2 * (2 : ℝ) ^ (T - T₁)) * (N p k ^ ε * J i))))) := by
  set R : ℝ := (2 : ℝ) ^ (T - T₁) with hR
  set δ : ℝ := N p k ^ (-(L p)) with hδ
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hNpos _
  have hNε : 0 < N p k ^ ε := Real.rpow_pos_of_pos hNpos _
  have hRpos : 0 < R := by positivity
  set Y := Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ with hYdef
  have hYm : MeasurableSet Y :=
    (measurableSet_Gwit hC u v P a e T₁ w b i).inter ((hA i).prod MeasurableSet.univ)
  have hi0 := mem_Sblk.mp hi
  -- `Y` lies in the incidence set of world `w`
  have hYE : Y ⊆ E p k w := by
    intro q hq
    have hq1 := hq.1
    simp only [Gwit, mem_iUnion] at hq1
    obtain ⟨i', hi', hq'⟩ := hq1
    have hi'' := mem_Sblk.mp (Finset.mem_filter.mp hi').1
    have := (hCsub i' hq').1
    rwa [hi''.1] at this
  have hνY : ((ν p k w).prod volume) Y = mu p k w Y := by
    show _ = (((ν p k w).prod volume).restrict (E p k w)) Y
    rw [Measure.restrict_apply hYm, Set.inter_eq_left.mpr hYE]
  rw [hνY]
  refine (measure_le_inter_add_sdiff (μ := mu p k w) (s := Y) (t := Exc p k w uu τ)).trans ?_
  gcongr
  -- the null set of unlisted witness labels
  set Null : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) := ⋃ i' ∈ Finset.univ.filter (fun i' => γ i' = w),
    {q | q ∈ C i' ∧ i' ∉ Λ w ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
      (⌊x q.1 q.2 / (N p k ^ (-(L p)))⌋ : ℤ))} with hNull
  have hNull0 : mu p k w Null = 0 := by
    apply le_antisymm _ zero_le
    refine (measure_biUnion_finset_le _ _).trans ?_
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i' hi'
    have hγ' : γ i' = w := (Finset.mem_filter.mp hi').2
    have := hΛae i'
    rw [hγ'] at this
    exact this
  -- the observation set
  set s₁ : ℝ := ((b : ℕ) : ℝ) / (2 : ℝ) ^ T₁ with hs₁
  set q1 : ℝ := ((2 : ℝ) ^ T₁)⁻¹ with hq1
  set Wd : ℝ := (1 + 2 * R) * (N p k ^ ε * J i) with hWd
  have hWd0 : 0 ≤ Wd := by have := hJ i; positivity
  set Kx : ℝ := 48 * R ^ 2 * N p k ^ ε with hKx
  have hKx0 : 0 ≤ Kx := by positivity
  set Strip : Set (Fin 2 → ℝ) :=
    {v' : Fin 2 → ℝ | (v' 0, v' 1) ∈
      Submission.Obl.k4_scalar_terminal_chart_packet_extraction.chartPar s₁ q1 (u i) (v i) Wd}
    with hStrip
  have hStripm : MeasurableSet Strip :=
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurableSet_chartPar
      s₁ q1 (u i) (v i) Wd).preimage (by fun_prop)
  set Hs : Set ((Fin 2 → ℝ) × ℤ) :=
    {o | |((o.2 : ℤ) : ℝ) - MvPolynomial.eval o.1 (P i) / δ| ≤ Kx + 1} with hHs
  have hHsm : MeasurableSet Hs := by
    refine measurableSet_le ?_ measurable_const
    have h2 : Measurable (fun o : (Fin 2 → ℝ) × ℤ => ((o.2 : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd
    have h3 : Measurable (fun o : (Fin 2 → ℝ) × ℤ => MvPolynomial.eval o.1 (P i) / δ) :=
      ((MvPolynomial.continuous_eval (P i)).measurable.comp measurable_fst).div_const δ
    exact (h2.sub h3).abs
  set Vf : Fin n → Finset ℤ := fun i' =>
    if i' ∈ Sblk p k T n γ j T₁ w b ∧ ¬ Agrees p k T₁ n u v P a e b i i' then Fb b i i'
    else ∅ with hVf
  set S' : Set (((Fin 2 → ℝ) × ℤ) × ℤ) :=
    {z | z.1.1 ∈ Strip ∧ z.1 ∈ Hs ∧ ∃ i', i' ∈ Λ w z.1 ∧ z.2 ∈ Vf i'} with hS'
  have hS'm : MeasurableSet S' := by
    have hangular : MeasurableSet {z : ((Fin 2 → ℝ) × ℤ) × ℤ | ∃ i', i' ∈ Λ w z.1 ∧ z.2 ∈ Vf i'} := by
      have he : {z : ((Fin 2 → ℝ) × ℤ) × ℤ | ∃ i', i' ∈ Λ w z.1 ∧ z.2 ∈ Vf i'} =
          ⋃ i', {z : ((Fin 2 → ℝ) × ℤ) × ℤ | i' ∈ Λ w z.1 ∧ z.2 ∈ Vf i'} := by ext z; simp
      rw [he]
      exact MeasurableSet.iUnion (fun i' =>
        ((hΛmeas w i').preimage measurable_fst).inter
          ((Vf i').countable_toSet.measurableSet.preimage measurable_snd))
    exact (hStripm.preimage (measurable_fst.comp measurable_fst)).inter
      ((hHsm.preimage measurable_fst).inter hangular)
  -- geometric membership of the observations of listed bad witnesses
  have hP : Y \ Null ⊆ obsA p k uu ⁻¹' S' := by
    intro q hq
    obtain ⟨⟨hqG, hqA⟩, hqN⟩ := hq
    simp only [Gwit, mem_iUnion] at hqG
    obtain ⟨i', hi', hqC⟩ := hqG
    obtain ⟨hi'S, hnag⟩ := Finset.mem_filter.mp hi'
    have hi'0 := mem_Sblk.mp hi'S
    have hqA' : q.1 ∈ A i := hqA.1
    have hqC' := (hCsub i' hqC).2
    have ht : q.2 ∈ I T₁ b := hi'0.2 hqC'.2
    have hlist : i' ∈ Λ w ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
        (⌊x q.1 q.2 / (N p k ^ (-(L p)))⌋ : ℤ)) := by
      by_contra hcon
      apply hqN
      simp only [hNull, mem_iUnion]
      exact ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'0.1⟩, hqC, hcon⟩
    refine ⟨?_, ?_, ?_⟩
    · -- the spatial strip
      show ((![q.2, y q.1 q.2] : Fin 2 → ℝ) 0, (![q.2, y q.1 q.2] : Fin 2 → ℝ) 1) ∈
        Submission.Obl.k4_scalar_terminal_chart_packet_extraction.chartPar s₁ q1 (u i) (v i) Wd
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by rw [I_eq_Icc] at ht; exact ht, ?_⟩
      have key := affine_extrap_block hT₁ hi0.2 (g := fun t => y q.1 t - u i - t * v i)
        (y_residual_affine q.1 (u i) (v i)) (E := N p k ^ ε * J i)
        (fun t ht' => (hfit i q.1 hqA' t ht').1) q.2 ht
      have : y q.1 q.2 - (u i + v i * q.2) = y q.1 q.2 - u i - q.2 * v i := by ring
      rw [this]
      exact key
    · -- the hidden-bin range
      show |((⌊x q.1 q.2 / δ⌋ : ℤ) : ℝ) -
        MvPolynomial.eval (![q.2, y q.1 q.2] : Fin 2 → ℝ) (P i) / δ| ≤ Kx + 1
      apply Submission.Obl.k4_scalar_terminal_chart_packet_extraction.floor_near_of_fit hδpos
      have key := quad_extrap_block hT₁ hi0.2
        (g := fun t => x q.1 t - MvPolynomial.eval ![t, y q.1 t] (P i))
        (x_residual_quad q.1 (P i) (hdeg i)) (E := N p k ^ ε * δ)
        (fun t ht' => (hfit i q.1 hqA' t ht').2) q.2 ht
      calc |x q.1 q.2 - MvPolynomial.eval ![q.2, y q.1 q.2] (P i)|
          ≤ 48 * R ^ 2 * (N p k ^ ε * δ) := key
        _ = Kx * δ := by rw [hKx]; ring
    · -- a listed witness label with its angular bins
      refine ⟨i', hlist, ?_⟩
      have hcond : i' ∈ Sblk p k T n γ j T₁ w b ∧ ¬ Agrees p k T₁ n u v P a e b i i' :=
        ⟨hi'S, hnag⟩
      show (⌊q.1.2 1 / (N p k ^ (-uu))⌋ : ℤ) ∈ Vf i'
      simp only [hVf, hcond, not_false_eq_true, and_self, ↓reduceIte]
      exact (hFb b i i' hi hi'S hnag).2 q.1 ⟨hqA', hqC'.1⟩
  -- the density estimate
  have hdens := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.mass_le_of_density_le
    (measurable_obsA p k uu) hGmeas hmap hS'm
    (ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ))) hP
  -- the reference measure
  have hfirst : ∀ x' ∈ Strip, Measure.count {j' : ℤ | (x', j') ∈ Hs} ≤
      ENNReal.ofReal (2 * (Kx + 1) + 1) := by
    intro x' _
    exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.count_int_near_le
      (MvPolynomial.eval x' (P i) / δ) (Kx + 1) (by linarith)
  have hlist : ∀ o, ((Λ w o).card : ℝ≥0∞) ≤ ENNReal.ofReal (N p k ^ ε) := by
    intro o
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hΛcard w o)
  have hbins' : ∀ i', ((Vf i').card : ℝ≥0∞) ≤ 6 := by
    intro i'
    by_cases hc : i' ∈ Sblk p k T n γ j T₁ w b ∧ ¬ Agrees p k T₁ n u v P a e b i i'
    · have h6 : (Vf i').card ≤ 6 := by
        simp only [hVf, hc, not_false_eq_true, and_self, ↓reduceIte]
        exact (hFb b i i' hi hc.1 hc.2).1
      exact_mod_cast h6
    · have h0 : Vf i' = ∅ := by simp only [hVf, hc, ↓reduceIte]
      rw [h0]; simp
  have href := listed_angular_reference_bound (volume : Measure (Fin 2 → ℝ)) Strip hStripm
    Hs hHsm (Λ w) (hΛmeas w) Vf _ _ _ hfirst hlist hbins'
  have hvol : volume Strip ≤ ENNReal.ofReal (q1 * (2 * Wd)) := by
    rw [hStrip, Submission.Obl.k4_scalar_terminal_chart_packet_extraction.volume_fin2_eq
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurableSet_chartPar
        s₁ q1 (u i) (v i) Wd)]
    exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.volume_chartPar_le
      s₁ q1 (u i) (v i) Wd hWd0
  calc mu p k w (Y \ Exc p k w uu τ)
      ≤ mu p k w (((Y \ Null) \ Exc p k w uu τ) ∪ Null) := by
        apply measure_mono
        intro q hq
        by_cases hqN : q ∈ Null
        · exact Or.inr hqN
        · exact Or.inl ⟨⟨hq.1, hqN⟩, hq.2⟩
    _ ≤ mu p k w ((Y \ Null) \ Exc p k w uu τ) + mu p k w Null := measure_union_le _ _
    _ = mu p k w ((Y \ Null) \ Exc p k w uu τ) := by rw [hNull0, add_zero]
    _ ≤ ENNReal.ofReal (N p k ^ (-f p (L p) - S p * uu + τ)) *
          ((volume.prod Measure.count).prod Measure.count) S' := hdens
    _ ≤ _ := by
        gcongr
        refine href.trans ?_
        gcongr

end Cap

end Submission.Obl.k4_scalar_angular_pair_agreement
