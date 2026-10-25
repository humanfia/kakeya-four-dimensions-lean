-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MultiplicityCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.ConvexTubeExtension
import Submission.WZ.Obl.wz_broad_grains_improvement.DenseCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion

namespace WangZahlLot.Obl.wz_broad_grains_improvement

set_option linter.unusedVariables false

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount bodyCount measurable_assignedFiber
    bodyCount_assignedFiber restrict_fiber_count_bounds body_mass_le_of_count
    fiberBodyCount_eq_ncard ball_subset_frozen_prism)

/-- Uniformly dense grains inside a `2c` ball inherit a convex count from the
fine tubes. The common fibre multiplicity saves a factor `m`; extending their
crossing segments costs `c⁻³`, and the local tube mass saves one power of `c`. -/
theorem grain_mass_count_of_katz_tao
    {δ h ρ a c b g m θ mK : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {G : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (h4 : 4 * δ ≤ c) (hm : 0 ≤ m) (hθ : 0 ≤ θ) (hmK : 0 ≤ mK)
    (hv : ∀ i, ‖v i‖ = 1) (hK : K δ mK n x v)
    (hZ : ∀ i, M (Z i) ∧ Z i ⊆ T δ (x i) (v i) ∧ (i ∉ S → Z i = ∅))
    (hH : HB δ h n x v S Z ρ N y w f a c b g L z e G γ m)
    (Q₀ : Finset (Fin L)) (z₀ : V)
    (hdense : ∀ j ∈ Q₀, O (θ * (a * (ρ * c) * c)) ≤ μ (G j))
    (hlocal : ∀ j ∈ Q₀, P a (ρ * c) c (z j) (e j) ⊆ closedBall z₀ (2 * c))
    {W : Set V} (hW : Convex ℝ W)
    (hQW : ∀ j ∈ Q₀, P a (ρ * c) c (z j) (e j) ⊆ W) :
    O (m * θ * Q₀.card * (a * (ρ * c) * c)) ≤
      O (3981312000 * mK / c ^ 2) * μ W := by
  classical
  rcases Q₀.eq_empty_or_nonempty with hQ | hQ
  · simp [hQ]
  obtain ⟨j₀, hj₀⟩ := hQ
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, _, hmult, hcross, _, _⟩ := hH
  have ha : 0 < a := hδ.trans_le hda
  have hc : 0 < c := by linarith
  have hδc : δ ≤ 2 * c := by linarith
  have hball : ball (z j₀) (δ / 2) ⊆ W :=
    (ball_subset_ball (by linarith : δ / 2 ≤ a / 2)).trans
      ((ball_subset_frozen_prism hab hbc (z j₀) (e j₀)).trans (hQW j₀ hj₀))
  have hzj : z j₀ ∈ W := hball (mem_ball_self (by positivity))
  have hWi : (interior W).Nonempty := ⟨z j₀,
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (ball_mem_nhds _ (by positivity : 0 < δ / 2)) hball)⟩
  let C₀ : Set V := wz_extremal_lipschitz_grains.enlarge (z j₀) (15 / c) W
  have hC₀conv : Convex ℝ C₀ := wz_extremal_lipschitz_grains.convex_enlarge hW _ _
  have hC₀vol : μ C₀ ≤ O (512 * (15 / c) ^ 3) * μ W :=
    volume_convex_enlarge_le hW hWi _ (by positivity)
  let G₀ : Fin L → Set V := fun j => if j ∈ Q₀ then G j else ∅
  let Z₀ : Fin n → Set V := fun i => Z i ∩ assignedFiber γ G₀ (f i)
  have hG₀mem (j : Fin L) (p : V) : p ∈ G₀ j ↔ j ∈ Q₀ ∧ p ∈ G j := by
    by_cases hj : j ∈ Q₀ <;> simp [G₀, hj]
  have hG₀m (j : Fin L) : M (G₀ j) := by
    by_cases hj : j ∈ Q₀ <;> simp only [G₀, hj, ite_true, ite_false]
    · exact (hgeom j).1
    · exact MeasurableSet.empty
  have hZ₀m (i : Fin n) : M (Z₀ i) :=
    (hZ i).1.inter (measurable_assignedFiber γ hG₀m (f i))
  have hG₀disj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (G₀ i) (G₀ j) := by
    intro i j hij hγ
    exact (hdisj i j hij hγ).mono
      (fun p hp => ((hG₀mem i p).mp hp).2) (fun p hp => ((hG₀mem j p).mp hp).2)
  have hlevel (k : Fin N) (p : V) (hp : p ∈ assignedFiber γ G₀ k) :
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    obtain ⟨j, hjk, hpj⟩ := hp
    have hpG := ((hG₀mem j p).mp hpj).2
    have hpZ : ∃ i ∈ S, f i = k ∧ p ∈ Z i := by
      have hmem : p ∈ {p | ∃ j, γ j = k ∧ p ∈ G j} := ⟨j, hjk, hpG⟩
      rwa [hunion k] at hmem
    have heq : {i : Fin n | f i = k ∧ p ∈ Z i} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext i
      constructor
      · rintro ⟨hik, hpi⟩
        refine ⟨?_, hik, hpi⟩
        by_contra hi
        simp [(hZ i).2.2 hi] at hpi
      · exact fun hi => hi.2
    rw [fiberBodyCount_eq_ncard, heq]
    exact hmult k p hpZ
  have hmass : O m * ∑ j, μ (G₀ j) ≤ ∑ i, μ (Z₀ i) := by
    apply body_mass_le_of_count hG₀m hZ₀m hm
    intro p
    have hh := (restrict_fiber_count_bounds f Z (assignedFiber γ G₀) hlevel p).1
    simpa only [bodyCount_assignedFiber γ G₀ hG₀disj p] using hh
  have hGmass : O (θ * Q₀.card * (a * (ρ * c) * c)) ≤ ∑ j, μ (G₀ j) := by
    have heq : (∑ j, μ (G₀ j)) = ∑ j ∈ Q₀, μ (G j) := by
      simp [G₀, apply_ite, Finset.sum_ite_mem]
    rw [heq]
    calc
      _ = ∑ _j ∈ Q₀, O (θ * (a * (ρ * c) * c)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg Q₀.card)]
        congr 1
        ring
      _ ≤ _ := Finset.sum_le_sum hdense
  let F₀ := Finset.univ.filter (fun i => (Z₀ i).Nonempty)
  have hcarrier (i : Fin n) (hi : i ∈ F₀) : T δ (x i) (v i) ⊆ C₀ := by
    obtain ⟨p, hpZ, j, hγ, hpG₀⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjQ, hpG⟩ := (hG₀mem j p).mp hpG₀
    have hiS : i ∈ S := by
      by_contra hi
      simp [(hZ i).2.2 hi] at hpZ
    have hcros := (hcross i hiS j hγ.symm ⟨p, hpZ, hpG⟩).2.2
    obtain ⟨p₀, hp₀, hcoord₀⟩ := hcros (-c / 2) (by simp)
    obtain ⟨p₁, hp₁, hcoord₁⟩ := hcros (c / 2) (by simp)
    apply tube_subset_convex_enlarge_of_contacts hW hδ h4 hc1 (hv i) hball hzj
      ⟨hp₀.1, hQW j hjQ hp₀.2⟩ ⟨hp₁.1, hQW j hjQ hp₁.2⟩
    have he : (e j (p₁ - p₀)) 2 = c := by
      have hsub : e j (p₁ - p₀) = e j (p₁ - z j) - e j (p₀ - z j) := by
        rw [← map_sub]
        congr 1
        abel
      rw [hsub]
      change (e j (p₁ - z j)) 2 - (e j (p₀ - z j)) 2 = c
      change (e j (p₀ - z j)) 2 = -c / 2 at hcoord₀
      change (e j (p₁ - z j)) 2 = c / 2 at hcoord₁
      rw [hcoord₀, hcoord₁]
      ring
    have hh := PiLp.norm_apply_le (e j (p₁ - p₀)) 2
    rw [Real.norm_eq_abs, he, abs_of_pos hc, (e j).norm_map] at hh
    simpa only [dist_eq_norm, norm_sub_rev] using hh
  have hcard : (F₀.card : ℝ) ≤ q n {i | T δ (x i) (v i) ⊆ C₀} := by
    exact_mod_cast Set.ncard_le_ncard (fun i hi => hcarrier i hi) (Set.toFinite _)
  have hKT : O (F₀.card * δ ^ 2) ≤ O mK * (O (512 * (15 / c) ^ 3) * μ W) := by
    calc
      _ ≤ O (q n {i | T δ (x i) (v i) ⊆ C₀} * δ ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))
      _ ≤ O mK * μ C₀ := hK C₀ hC₀conv
      _ ≤ _ := mul_le_mul' le_rfl hC₀vol
  have hZ₀sub (i : Fin n) : Z₀ i ⊆ T δ (x i) (v i) ∩ closedBall z₀ (2 * c) := by
    rintro p ⟨hpZ, j, hjf, hpG₀⟩
    obtain ⟨hjQ, hpG⟩ := (hG₀mem j p).mp hpG₀
    exact ⟨(hZ i).2.1 hpZ, hlocal j hjQ ((hgeom j).2.1 hpG)⟩
  have hZmass : (∑ i, μ (Z₀ i)) ≤ O (2304 * c) * O (F₀.card * δ ^ 2) := by
    calc
      _ ≤ ∑ i, if i ∈ F₀ then O (1152 * (2 * c) * δ ^ 2) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ F₀
        · rw [ite_eq_left hi]
          exact (measure_mono (hZ₀sub i)).trans
            (wz_normalized_projection_iteration.tube_inter_ball_volume_le hδ hδc
              (x i) (v i) z₀ (hv i))
        · rw [ite_eq_right hi]
          have he : Z₀ i = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp
            intro hn
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
          simp [he]
      _ = O (2304 * c) * O (F₀.card * δ ^ 2) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg F₀.card),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  calc
    _ = O m * O (θ * Q₀.card * (a * (ρ * c) * c)) := by
      rw [← ENNReal.ofReal_mul hm]
      congr 1
      ring
    _ ≤ O m * ∑ j, μ (G₀ j) := mul_le_mul' le_rfl hGmass
    _ ≤ ∑ i, μ (Z₀ i) := hmass
    _ ≤ O (2304 * c) * O (F₀.card * δ ^ 2) := hZmass
    _ ≤ O (2304 * c) * (O mK * (O (512 * (15 / c) ^ 3) * μ W)) :=
      mul_le_mul' le_rfl hKT
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
      ring

/-- The exact local convex-count clause of `H`, on any uniformly dense
subfamily, with its coefficient expressed through the fine KT constant. -/
theorem local_grain_count_of_katz_tao
    {δ h ρ a c b g m θ mK : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {G : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (h4 : 4 * δ ≤ c) (hm : 0 < m) (hθ : 0 < θ) (hmK : 0 ≤ mK)
    (hv : ∀ i, ‖v i‖ = 1) (hK : K δ mK n x v)
    (hZ : ∀ i, M (Z i) ∧ Z i ⊆ T δ (x i) (v i) ∧ (i ∉ S → Z i = ∅))
    (hH : HB δ h n x v S Z ρ N y w f a c b g L z e G γ m)
    (Q₀ : Finset (Fin L))
    (hdense : ∀ j ∈ Q₀, O (θ * (a * (ρ * c) * c)) ≤ μ (G j)) :
    ∀ j W, Convex ℝ W →
      O (q L {j' | j' ∈ Q₀ ∧
        P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤
      O (3981312000 * mK / (m * θ * c ^ 2)) * μ W := by
  classical
  intro j W hW
  have ha : 0 < a := hδ.trans_le hH.1
  have hrc : 0 < ρ * c := ha.trans_le hH.2.1
  have hc : 0 < c := hrc.trans_le hH.2.2.1
  have hρ : 0 < ρ := pos_of_mul_pos_left hrc hc.le
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hc).mp (by simpa using hH.2.2.1)
  have haρ : a ≤ a / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  have harc : 2 * a / ρ ≤ 2 * c := (div_le_iff₀ hρ).mpr (by nlinarith [hH.2.1])
  let Q₁ := Q₀.filter (fun j' =>
    P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
    P a (ρ * c) c (z j') (e j') ⊆ W)
  have hQ₁ (j' : Fin L) (hj' : j' ∈ Q₁) :
      j' ∈ Q₀ ∧
      P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
      P a (ρ * c) c (z j') (e j') ⊆ W := Finset.mem_filter.mp hj'
  have hlocal (j' : Fin L) (hj' : j' ∈ Q₁) :
      P a (ρ * c) c (z j') (e j') ⊆ closedBall (z j) (2 * c) := by
    apply Set.Subset.trans ?_ ((hQ₁ j' hj').2.1.trans
      (wz_two_scale_flat_box_estimate.box_subset_closedBall harc le_rfl (by positivity) _ _))
    rintro p ⟨hp₀, hp₁, hp₂⟩
    exact ⟨hp₀.trans (by linarith), hp₁.trans (by linarith [hH.2.2.1]), hp₂⟩
  have hb := grain_mass_count_of_katz_tao hδ h4 hm.le hθ.le hmK hv hK hZ hH Q₁ (z j)
    (fun j' hj' => hdense j' (hQ₁ j' hj').1) hlocal hW (fun j' hj' => (hQ₁ j' hj').2.2)
  have heq : q L {j' | j' ∈ Q₀ ∧
      P (a / ρ) c c (z j') (e j') ⊆ P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
      P a (ρ * c) c (z j') (e j') ⊆ W} = Q₁.card := by
    simp only [q, ← Set.ncard_coe_finset Q₁]
    congr 2
    ext j'
    simp [Q₁]
  rw [heq]
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr
    (show 0 < m * θ by positivity)).ne' ENNReal.ofReal_ne_top).mp
  convert hb using 1
  · rw [← ENNReal.ofReal_mul (show 0 ≤ m * θ by positivity)]
    congr 1
    ring
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (show 0 ≤ m * θ by positivity)]
    congr 2
    field_simp

end WangZahlLot.Obl.wz_broad_grains_improvement
