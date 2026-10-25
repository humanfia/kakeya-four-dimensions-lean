-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Setup.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Normalize
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSCubes
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.CoarsePerturb

/-!
# The fine data used in one application of the slab lemma

`FineSetup` collects the properties of a refined fine family that the construction of the
coarse sets uses: global and local grains of the original union `Eo`, the plane map, the
shadings `Y` (a refinement) inside non-horizontal tubes, and the bound `N` on the number of
shadings meeting a grid cube of side `s`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- The fine data of the slab construction. -/
structure FineSetup (σ δ s θ K N : ℝ) {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (Eo : Set Space) (f : ℝ → ℝ) (P : Space → Space) : Prop where
  σ_pos : 0 < σ
  σ_lt : σ < 1
  δ_pos : 0 < δ
  δ_le : δ ≤ s
  s_small : s ≤ 1 / 10 ^ 6
  θ_pos : 0 < θ
  θ_le : θ ≤ 1
  K_one : 1 ≤ K
  f_lip : LipschitzWith 1 f
  f_bound : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 3
  P_lip : LipschitzWith 1 P
  Eo_ball : Eo ⊆ ball 0 1
  glob : ∀ z ∈ Icc (-1 : ℝ) 1, Reg.Assouad δ (1 - σ) K (Reg.ProjectedSlice f Eo z)
  loc : ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∀ p ∈ Eo,
    Reg.Assouad r (1 - σ) K ((fun q : Space => ⟪P p, q⟫) '' (Eo ∩ ball p (Real.sqrt r)))
  unit : ∀ p ∈ Eo, ‖P p‖ = 1
  meas : ∀ i, MeasurableSet (Y i)
  sub_Eo : ∀ i, Y i ⊆ Eo
  sub_tube : ∀ i, Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i))
  v_unit : ∀ i, ‖v i‖ = 1
  perp : ∀ i, ∀ p ∈ Y i, |⟪v i, P p⟫| ≤ δ
  vert : ∀ i, (Y i).Nonempty → θ ≤ |v i 2|
  cube : ∀ k : Fin 3 → ℤ, (({i | (Y i ∩ Coarse.gridCube s k).Nonempty}.ncard : ℕ) : ℝ) ≤ N

lemma abs_coord_le (p : Space) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  have := PiLp.norm_apply_le p i
  simpa [Real.norm_eq_abs] using this

lemma abs_coord_sub_le (p q : Space) (i : Fin 3) : |p i - q i| ≤ dist p q := by
  rw [dist_eq_norm]
  have := abs_coord_le (p - q) i
  simpa using this

lemma abs_coord_lt_one {p : Space} (hp : p ∈ ball (0 : Space) 1) (i : Fin 3) : |p i| < 1 := by
  have h := mem_ball_zero_iff.mp hp
  exact (abs_coord_le p i).trans_lt h

/-- Two points of a quantitatively non-horizontal tube are close when their heights are. -/
lemma tube_pair_dist {δ θ : ℝ} {x v p q : Space} (hθ : 0 < θ) (hv : ‖v‖ = 1)
    (hvθ : θ ≤ |v 2|) (hp : p ∈ thickening δ (segment ℝ x (x + v)))
    (hq : q ∈ thickening δ (segment ℝ x (x + v))) :
    dist p q ≤ (|p 2 - q 2| + 2 * δ) / θ + 2 * δ := by
  obtain ⟨t, -, ht⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  obtain ⟨t', -, ht'⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  have hv2 : 0 < |v 2| := hθ.trans_le hvθ
  have e1 : (x + t • v) - (x + t' • v) = (t - t') • v := by module
  have hdiff : ‖(x + t • v) - (x + t' • v)‖ = |t - t'| := by
    rw [e1, norm_smul, hv, mul_one, Real.norm_eq_abs]
  -- the parameter difference is controlled by the height difference
  have hpar : |t - t'| * |v 2| ≤ |p 2 - q 2| + 2 * δ := by
    have h2 : ((x + t • v) - (x + t' • v)) 2 = (t - t') * v 2 := by
      rw [e1]; simp
    have hc1 := abs_coord_le (p - (x + t • v)) 2
    have hc2 := abs_coord_le (q - (x + t' • v)) 2
    simp only [PiLp.sub_apply] at hc1 hc2
    have : (t - t') * v 2 = (p 2 - q 2) - (p 2 - (x + t • v) 2) + (q 2 - (x + t' • v) 2) := by
      rw [← h2]; simp only [PiLp.sub_apply]; ring
    rw [← abs_mul, this]
    calc |(p 2 - q 2) - (p 2 - (x + t • v) 2) + (q 2 - (x + t' • v) 2)|
        ≤ |p 2 - q 2| + |p 2 - (x + t • v) 2| + |q 2 - (x + t' • v) 2| := by
          have := abs_add_le ((p 2 - q 2) - (p 2 - (x + t • v) 2)) (q 2 - (x + t' • v) 2)
          have := abs_sub (p 2 - q 2) (p 2 - (x + t • v) 2)
          linarith
      _ ≤ |p 2 - q 2| + 2 * δ := by linarith
  have ht'' : |t - t'| ≤ (|p 2 - q 2| + 2 * δ) / θ := by
    rw [le_div_iff₀ hθ]
    calc |t - t'| * θ ≤ |t - t'| * |v 2| := mul_le_mul_of_nonneg_left hvθ (abs_nonneg _)
      _ ≤ _ := hpar
  calc dist p q = ‖(p - (x + t • v)) + ((x + t • v) - (x + t' • v)) + ((x + t' • v) - q)‖ := by
        rw [dist_eq_norm]; congr 1; abel
    _ ≤ ‖p - (x + t • v)‖ + ‖(x + t • v) - (x + t' • v)‖ + ‖(x + t' • v) - q‖ :=
        norm_add₃_le
    _ ≤ δ + (|p 2 - q 2| + 2 * δ) / θ + δ := by
        have h3 : ‖(x + t' • v) - q‖ < δ := by rw [norm_sub_rev]; exact ht'
        rw [hdiff]
        linarith
    _ = (|p 2 - q 2| + 2 * δ) / θ + 2 * δ := by ring

/-- Twisted coordinates of nearby points with nearby slopes are close. -/
lemma twist_sub_le {p q : Space} {F G : ℝ} (hF : |F| ≤ 3) (hq1 : |q 1| ≤ 1) :
    |(p 0 + F * p 1) - (q 0 + G * q 1)| ≤ 4 * dist p q + |F - G| := by
  have h0 := abs_coord_sub_le p q 0
  have h1 := abs_coord_sub_le p q 1
  have e : (p 0 + F * p 1) - (q 0 + G * q 1) = (p 0 - q 0) + F * (p 1 - q 1) + (F - G) * q 1 := by
    ring
  rw [e]
  calc |(p 0 - q 0) + F * (p 1 - q 1) + (F - G) * q 1|
      ≤ |(p 0 - q 0) + F * (p 1 - q 1)| + |(F - G) * q 1| := abs_add_le _ _
    _ ≤ |p 0 - q 0| + |F * (p 1 - q 1)| + |(F - G) * q 1| := by
        gcongr; exact abs_add_le _ _
    _ = |p 0 - q 0| + |F| * |p 1 - q 1| + |F - G| * |q 1| := by rw [abs_mul, abs_mul]
    _ ≤ dist p q + 3 * dist p q + |F - G| * 1 := by
        gcongr
    _ = 4 * dist p q + |F - G| := by ring

lemma mem_projectedSlice {f : ℝ → ℝ} {E : Set Space} {q : Space} (hq : q ∈ E) :
    q 0 + f (q 2) * q 1 ∈ Reg.ProjectedSlice f E (q 2) :=
  ⟨q, hq, rfl⟩

lemma projectedSlice_subset_Icc {f : ℝ → ℝ} {E : Set Space} (hE : E ⊆ ball 0 1) {z : ℝ}
    (hfz : |f z| ≤ 3) : Reg.ProjectedSlice f E z ⊆ Icc (-4) 4 := by
  rintro u ⟨q, hq, he⟩
  obtain ⟨hu, hz⟩ := Prod.mk.inj he
  have h0 := abs_coord_lt_one (hE hq) 0
  have h1 := abs_coord_lt_one (hE hq) 1
  rw [← hu, mem_Icc, ← abs_le, hz]
  calc |q 0 + f z * q 1| ≤ |q 0| + |f z| * |q 1| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 + 3 * 1 := by gcongr
    _ = 4 := by norm_num

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
