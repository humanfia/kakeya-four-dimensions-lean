-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.DenseCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.ThickGrains

/-!
# Unpacked frozen grains, and the dense-grain cut

`HB` is the body of the frozen grains predicate `H` for explicit grain data.
`dense_cut` removes the grains of density below `δ^h/2` (they become empty, the
boxes and indices stay) and cuts every fine shading to the surviving grains of
its fibre.  All clauses of `H` survive with the error weakened by a factor two
in the grain mass, the fine mass drops by at most a factor four, and the fibre
counts are unchanged at every retained point.  Afterwards every nonempty grain
has density at least `δ^h/2` in its box, so grains can be selected freely.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set Metric
open scoped ENNReal

/-- The body of the frozen grains predicate for explicit grain data. -/
def HB (d h : ℝ) (n : ℕ) (x v : Fin n → V) (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ)
    (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N) (a c b g : ℝ) (L : ℕ) (z : Fin L → V)
    (e : Fin L → V ≃ₗᵢ[ℝ] V) (G : Fin L → Set V) (γ : Fin L → Fin N) (m : ℝ) : Prop :=
  d ≤ a ∧ a ≤ ρ * c ∧ ρ * c ≤ c ∧ c ≤ 1 ∧
  (∀ j, M (G j) ∧ G j ⊆ P a (ρ * c) c (z j) (e j) ∧
    P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
    ι (e j (w (γ j))) 0 ^ 2 + ι (e j (w (γ j))) 1 ^ 2 ≤ (10 * ρ) ^ 2) ∧
  (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (G j) (G j')) ∧
  (∀ k, {p | ∃ j, γ j = k ∧ p ∈ G j} = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i}) ∧
  O (d ^ h * L * a * (ρ * c) * c) ≤ ∑ j, μ (G j) ∧
  (∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
    q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Set.Icc m (2 * m)) ∧
  (∀ i ∈ S, ∀ j, f i = γ j → (Z i ∩ G j).Nonempty →
    Z i ∩ P a (ρ * c) c (z j) (e j) ⊆ G j ∧
    (∀ p ∈ T d (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
      |ι (e j (p - z j)) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T d (x i) (v i) ∩ P a (ρ * c) c (z j) (e j), ι (e j (p - z j)) 2 = t) ∧
  b ≤ c ∧
  ∀ j W, Convex ℝ W →
    O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
      P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O g * μ W

theorem H_iff {d h : ℝ} {n : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {ρ : ℝ} {N : ℕ} {y w : Fin N → V} {f : Fin n → Fin N} {a c b g : ℝ} :
    H d h n x v S Z ρ N y w f a c b g ↔
      ∃ (L : ℕ) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (G : Fin L → Set V)
        (γ : Fin L → Fin N) (m : ℝ), HB d h n x v S Z ρ N y w f a c b g L z e G γ m :=
  Iff.rfl

/-- Fibre membership is unchanged at the retained points of a common fibre cut. -/
lemma mem_cut_iff {n N : ℕ} {f : Fin n → Fin N} {Z : Fin n → Set V} {C' : Fin N → Set V}
    {i : Fin n} {p : V} (hp : p ∈ C' (f i)) : p ∈ Z i ∩ C' (f i) ↔ p ∈ Z i :=
  ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩

/-- The fibre sets of a common fibre cut, at a point of the cut. -/
lemma cut_fibre_set {n N : ℕ} {f : Fin n → Fin N} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {C' : Fin N → Set V} {k : Fin N} {p : V} (hp : p ∈ C' k) (R : Fin n → Prop) :
    {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ C' (f i) ∧ R i} = {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ R i} := by
  ext i
  constructor
  · rintro ⟨hS, hk, hZ, hR⟩
    exact ⟨hS, hk, hZ.1, hR⟩
  · rintro ⟨hS, hk, hZ, hR⟩
    exact ⟨hS, hk, ⟨hZ, hk ▸ hp⟩, hR⟩

/-- Away from the cut, a fibre has no retained tubes. -/
lemma cut_fibre_empty {n N : ℕ} {f : Fin n → Fin N} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {C' : Fin N → Set V} {k : Fin N} {p : V} (hp : p ∉ C' k) (R : Fin n → Prop) :
    {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ C' (f i) ∧ R i} = ∅ := by
  ext i
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨-, hk, hZ, -⟩
  exact hp (hk ▸ hZ.2)

/-- **Dense-grain cut.** Grains of density below `δ^h/2` are emptied and every fine
shading is cut to the surviving grains of its fibre. -/
theorem dense_cut {d h h' ρ a c b g m : ℝ} {n N L : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {G : Fin L → Set V} {γ : Fin L → Fin N}
    (hd : 0 < d) (hh' : d ^ h' ≤ d ^ h / 2)
    (hZ : ∀ i, M (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅))
    (hH : HB d h n x v S Z ρ N y w f a c b g L z e G γ m) :
    ∃ G' : Fin L → Set V,
      (∀ j, G' j ⊆ G j) ∧
      (∀ j, G' j ≠ ∅ → O (d ^ h / 2) * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (G' j)) ∧
      (∀ i, M (Z i ∩ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ G' (f i))) ∧
      O (1 / 4) * ∑ i, μ (Z i) ≤
        ∑ i, μ (Z i ∩ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ G' (f i)) ∧
      HB d h' n x v S
        (fun i => Z i ∩ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ G' (f i))
        ρ N y w f a c b g L z e G' γ m := by
  classical
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmassG, hmult, hcross, hb, hcount⟩ := hH
  have ha : 0 < a := hd.trans_le hda
  have hρc : 0 < ρ * c := ha.trans_le hab
  have hcpos : 0 < c := hρc.trans_le hbc
  let U : Fin L → Set V := fun j => P a (ρ * c) c (z j) (e j)
  have hUvol : ∀ j, volume (U j) = O (a * (ρ * c) * c) := fun j =>
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hρc.le hcpos.le (z j) (e j)
  have hGm : ∀ j, MeasurableSet (G j) := fun j => (hgeom j).1
  have hGU : ∀ j, G j ⊆ U j := fun j => (hgeom j).2.1
  have hGfin : (∑ j, volume (G j)) ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro j _
    apply lt_of_le_of_lt (measure_mono (hGU j))
    rw [hUvol j]
    exact ENNReal.ofReal_lt_top
  have hbudget : (∑ j, O (d ^ h / 2) * volume (U j)) ≤
      (1 / 2 : ℝ≥0∞) * ∑ j, volume (G j) := by
    calc (∑ j, O (d ^ h / 2) * volume (U j))
        = ∑ _j : Fin L, O (d ^ h / 2 * (a * (ρ * c) * c)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hUvol j, ← ENNReal.ofReal_mul (by positivity)]
      _ = O (L * (d ^ h / 2 * (a * (ρ * c) * c))) := sum_const_ofReal L _
      _ = O (1 / 2) * O (d ^ h * L * a * (ρ * c) * c) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ (1 / 2 : ℝ≥0∞) * ∑ j, volume (G j) := by
          rw [ofReal_half]
          exact mul_le_mul' le_rfl hmassG
  obtain ⟨G', hG', hG'mass, hG'dense⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.dense_individual_refinement G U hGm hGfin
      hbudget
  have hG'm : ∀ j, MeasurableSet (G' j) := fun j => (hG' j).1
  have hG'G : ∀ j, G' j ⊆ G j := fun j => (hG' j).2
  -- fibre language of o095
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i hi => (hZ i).2.2 hi
  have heq : ∀ k, WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ G k =
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z k := by
    intro k
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport k]
    exact hunion k
  obtain ⟨m', hm'0, hlevel⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.fine_level_of_UF hsupport ⟨m, hmult⟩
  set C' := WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ G' with hC'
  have hC'm : ∀ k, MeasurableSet (C' k) :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.measurable_assignedFiber γ hG'm
  have hC'Z : ∀ k, C' k ⊆ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z k :=
    fun k => (WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_mono γ hG'G k).trans
      (heq k).subset
  have hretain : O (1 / 2) * ∑ j, volume (G j) ≤ ∑ j, volume (G' j) := by
    rw [ofReal_half]
    exact hG'mass
  obtain ⟨W₀, hW₀, hW₀mass, hW₀fib⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_refinement_transfer f γ Z G G'
      hm'0 (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun i => (hZ i).1) hGm hG'm hG'G hdisj heq hlevel
      hretain
  -- the explicit cut
  let Z' : Fin n → Set V := fun i => Z i ∩ C' (f i)
  have hZ'm : ∀ i, MeasurableSet (Z' i) := fun i => (hZ i).1.inter (hC'm (f i))
  have hW₀Z' : ∀ i, W₀ i ⊆ Z' i := by
    intro i p hp
    refine ⟨(hW₀ i).2 hp, ?_⟩
    have : p ∈ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f W₀ (f i) :=
      ⟨i, rfl, hp⟩
    rwa [hW₀fib] at this
  have hZ'mass : O (1 / 4) * ∑ i, μ (Z i) ≤ ∑ i, μ (Z' i) := by
    have h1 : O (1 / 2 / 2) * ∑ i, volume (Z i) ≤ ∑ i, volume (W₀ i) := hW₀mass
    calc O (1 / 4) * ∑ i, μ (Z i) = O (1 / 2 / 2) * ∑ i, volume (Z i) := by norm_num
      _ ≤ ∑ i, volume (W₀ i) := h1
      _ ≤ ∑ i, μ (Z' i) := Finset.sum_le_sum fun i _ => measure_mono (hW₀Z' i)
  have hfibZ' : ∀ k, WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z' k = C' k :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_restrict f Z C' hC'Z
  refine ⟨G', hG'G, hG'dense, hZ'm, hZ'mass, ?_⟩
  -- the clauses of HB for the cut
  refine ⟨hda, hab, hbc, hc1, ?_, ?_, ?_, ?_, ?_, ?_, hb, hcount⟩
  · intro j
    exact ⟨hG'm j, (hG'G j).trans (hGU j), (hgeom j).2.2.1, (hgeom j).2.2.2⟩
  · intro j j' hjj' hγ
    exact (hdisj j j' hjj' hγ).mono (hG'G j) (hG'G j')
  · intro k
    have h1 := hfibZ' k
    ext p
    constructor
    · intro hp
      have hp' : p ∈ C' k := hp
      rw [← h1] at hp'
      obtain ⟨i, hik, hpi⟩ := hp'
      have hiS : i ∈ S := by
        by_contra hnot
        have := hpi.1
        rw [hsupport i hnot] at this
        exact this
      exact ⟨i, hiS, hik, hpi⟩
    · rintro ⟨i, -, hik, hpi⟩
      have : p ∈ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z' k :=
        ⟨i, hik, hpi⟩
      rw [h1] at this
      exact this
  · calc O (d ^ h' * L * a * (ρ * c) * c)
        ≤ O (1 / 2) * O (d ^ h * L * a * (ρ * c) * c) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          have hpos : (0 : ℝ) ≤ L * a * (ρ * c) * c := by positivity
          calc d ^ h' * L * a * (ρ * c) * c = d ^ h' * (L * a * (ρ * c) * c) := by ring
            _ ≤ d ^ h / 2 * (L * a * (ρ * c) * c) := mul_le_mul_of_nonneg_right hh' hpos
            _ = 1 / 2 * (d ^ h * L * a * (ρ * c) * c) := by ring
      _ ≤ O (1 / 2) * ∑ j, volume (G j) := mul_le_mul' le_rfl hmassG
      _ ≤ ∑ j, volume (G' j) := hretain
  · intro k p hp
    obtain ⟨i, hiS, hik, hpi⟩ := hp
    have hpC : p ∈ C' k := hik ▸ hpi.2
    have hset := cut_fibre_set (S := S) (Z := Z) (f := f) hpC (fun _ => True)
    simp only [and_true] at hset
    rw [hset]
    exact hmult k p ⟨i, hiS, hik, hpi.1⟩
  · intro i hiS j hij hne
    obtain ⟨p₀, hp₀Z, hp₀G⟩ := hne
    have hne' : (Z i ∩ G j).Nonempty := ⟨p₀, hp₀Z.1, hG'G j hp₀G⟩
    obtain ⟨hsub, hfront, htwo⟩ := hcross i hiS j hij hne'
    refine ⟨?_, hfront, htwo⟩
    rintro p ⟨hpZ', hpU⟩
    have hpG : p ∈ G j := hsub ⟨hpZ'.1, hpU⟩
    have hpC : p ∈ C' (f i) := hpZ'.2
    obtain ⟨j', hj'k, hpj'⟩ := hpC
    by_cases hjj : j' = j
    · exact hjj ▸ hpj'
    · exact absurd (hdisj j' j hjj (hj'k.trans hij)) (Set.not_disjoint_iff.mpr
        ⟨p, hG'G j' hpj', hpG⟩)

end WangZahlLot.Obl.wz_broad_grains_improvement
