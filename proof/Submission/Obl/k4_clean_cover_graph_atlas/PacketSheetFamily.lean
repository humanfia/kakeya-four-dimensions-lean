import Submission.Obl.k4_clean_cover_graph_atlas.PacketBounds
import Submission.Obl.k4_clean_cover_graph_atlas.PacketCertificate
import Submission.Obl.k4_clean_cover_graph_atlas.InitialScale
import Submission.Obl.k4_clean_cover_graph_atlas.NormalizedBounds

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MvPolynomial Set MeasureTheory Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- Along a physical trajectory, the comparison coordinates reconstruct exactly
the normalized point, including its hidden coordinate. -/
theorem comparisonCurvePoint_groupBase {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {centre : Real3} {radius : ℝ} (hr : radius ≠ 0)
    (B δ' : ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    comparisonCurvePoint centre radius (groupBase T j c u Q centre radius (obs B δ' (l, t)))
      (B * gx l t 3) = normPt T j c u Q B l t := by
  unfold comparisonCurvePoint
  rw [← normBase_eq_center_add hr B δ' (l, t), normBase_eq_init T j c u Q B l t]
  have hh := snoc_init_eq (normPt T j c u Q B l t)
  exact hh

/-- The group base of a physical point is independent of the hidden-bin scale. -/
theorem groupBase_obs_independent (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (centre : Real3) (radius B a B' a' : ℝ)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    groupBase T j c u Q centre radius (obs B a p) =
      groupBase T j c u Q centre radius (obs B' a' p) := by
  unfold groupBase
  rw [normBaseObs_obs, normBaseObs_obs]

/-- Sheet data for one physical packet family, including its whole-block fit and
both bounds on the selected physical derivative scale. -/
def PacketLineSheetCertificate (Csheet : ℕ) (A U δfit : ℝ) (T j s₀ jj : ℕ)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (Bv : ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (k : Fin 2 → ℤ) (S : Set (ℕ × (Fin 6 → ℝ)))
    (l0 : ℕ × (Fin 6 → ℝ)) (t0 : ℝ) (flat : Bool) (F : RealSheet 2) (σ : ℝ) : Prop :=
      (flat = false ↔ |qc (normPoly T j c u Q Bv P) / 2| * (U * δfit / A) ≤ A ^ (-20 : ℝ)) ∧
      NormalizedRootCertificate (normPoly T j c u Q Bv P) flat F (subBoxCenter s₀ jj k)
        (A ^ (-(Csheet : ℝ)) / 128) σ ∧
      σ = eval (normPt T j c u Q Bv l0 t0)
        (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q Bv P))) ∧
      (∀ l ∈ S, ∀ t ∈ subBlock T s₀ j jj,
        |Bv * gx l t 3 - (F.f (emb (groupBase T j c u Q (subBoxCenter s₀ jj k)
          (A ^ (-(Csheet : ℝ)) / 128) (obs Bv δfit (l, t))))).re| ≤
          U * δfit * A ^ ((Csheet : ℝ) + 1)) ∧
      (let sc := selectedSlopeFactor flat Bv * |σ|
       0 < sc ∧ sc ≤ Bv * A + Bv ^ 2 * |qc (normPoly T j c u Q Bv P)| ∧
         sc⁻¹ ≤ A / Bv + A ^ (20 : ℕ) / Bv ^ 2)

/-- Select one actual sheet for a family of packet lines with a common midpoint
sign bit. The input is in physical coordinates; all output fits use group coordinates. -/
def PacketSheetFamilyAt (Csheet : ℕ) : Prop :=
    ∀ {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T j : ℕ} {rold Bv : ℝ}
      {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
      {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {Aold : Set (ℕ × (Fin 6 → ℝ))}
      {Fold : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop},
    gchart Nk M D κ T (j : ℝ) rold Bv Ev c u Q R Aold Fold ex → 0 < Bv →
    ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
    ∀ {A U δfit : ℝ}, 2 ≤ A → 0 < U → 4 * U ≤ A → κ + 1 ≤ A → 0 < δfit → δfit ≤ 1 →
    (∀ e, |(qbPoly (normPoly T j c u Q Bv P) * qbPoly (normPoly T j c u Q Bv P) -
      MvPolynomial.C (2 * qc (normPoly T j c u Q Bv P)) * qcPoly (normPoly T j c u Q Bv P)).coeff e| ≤ A) →
    ∀ {s₀ jj : ℕ} (k : Fin 2 → ℤ), jj < 2 ^ s₀ →
    side s₀ * (κ + 2) ≤ (A ^ (-(Csheet : ℝ)) / 128) / 2 →
    ∀ (S : Set (ℕ × (Fin 6 → ℝ))),
    (∀ l ∈ S, l ∈ Aold ∧ inBox s₀ k (zc Q c u l (subMid T s₀ j jj))) →
    (∀ l ∈ S, ∀ t ∈ Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T),
      |eval (gx l t) P| ≤ U * δfit ∧ |eval (gx l t) (pderiv 3 P)| ≤ U * Bv) →
    ∀ (l0 : ℕ × (Fin 6 → ℝ)) (t0 : ℝ), l0 ∈ S → t0 ∈ subBlock T s₀ j jj →
    Bv / U ≤ |eval (gx l0 t0) (pderiv 3 P)| →
    (∀ l ∈ S, decide (0 ≤ eval (gx l (subMid T s₀ j jj)) (pderiv 3 P)) =
      decide (0 ≤ eval (gx l0 (subMid T s₀ j jj)) (pderiv 3 P))) →
    ∃ (flat : Bool) (F : RealSheet 2) (σ : ℝ),
      PacketLineSheetCertificate Csheet A U δfit T j s₀ jj c u Q Bv P k S l0 t0 flat F σ

/-- Stable sheets construct comparison sheets for physical packet line families. -/
theorem exists_packet_sheet_for_lines (h : stableSheets) :
    ∃ Csheet : ℕ, 20 ≤ Csheet ∧ PacketSheetFamilyAt Csheet := by
  obtain ⟨Csheet, hCsheet, hchoose⟩ := exists_comparison_sheet_for_curves h
  refine ⟨Csheet, hCsheet, ?_⟩
  intro Nk M D κ T j rold Bv Ev c u Q R Aold Fold ex hchart hB P hP
    A U δfit hA hU hUA hκA hδ hδ1 hcoeff s₀ jj k hjj hside S hS htests l0 t0 hl0 ht0 hregular hbit
  let radius := A ^ (-(Csheet : ℝ)) / 128
  let centre := subBoxCenter s₀ jj k
  let Pb := normPoly T j c u Q Bv P
  let ta := (subIdx s₀ j jj : ℝ) / (2 : ℝ) ^ (T + s₀)
  let tb := ((subIdx s₀ j jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀)
  let base : S → ℝ → Real3 := fun l t => groupBase T j c u Q centre radius (obs Bv δfit (l.val, t))
  let hidden : S → ℝ → ℝ := fun l t => Bv * gx l.val t 3
  have hApos : 0 < A := by linarith
  have hradius : 0 < radius := by dsimp only [radius]; positivity
  have hUle : U ≤ A := by linarith
  have hfit : 0 < U * δfit / A := by positivity
  have hfit1 : U * δfit / A ≤ 1 := (div_le_one hApos).mpr
    ((mul_le_mul_of_nonneg_left hδ1 hU.le).trans (by simpa using hUle))
  have hQ : Q.det ≠ 0 := hchart.1
  have hPb : Pb.totalDegree ≤ 2 := (normPoly_totalDegree_le T j c u Q Bv P).trans hP
  have heq (l : S) (t : ℝ) : comparisonCurvePoint centre radius (base l t) (hidden l t) =
      normPt T j c u Q Bv l.val t := by
    dsimp only [base, hidden]
    exact comparisonCurvePoint_groupBase (T := T) (j := j) (c := c) (u := u) (Q := Q)
      (centre := centre) hradius.ne' Bv δfit l.val t
  have hhalf (l : S) (t : ℝ) (ht : t ∈ Icc ta tb) : ‖base l t‖ ≤ 1 / 2 := by
    exact groupBase_mem_halfBall (s₀ := s₀) (jj := jj) (k := k) (p := (l.val, t))
      hchart hradius hside (hS l.val l.property).1 (hS l.val l.property).2 ht Bv δfit
  have hbounds (l : S) (t : ℝ) (ht : t ∈ Icc ta tb) :
      |eval (comparisonCurvePoint centre radius (base l t) (hidden l t)) Pb| ≤ (U * δfit / A) * A ∧
      |eval (comparisonCurvePoint centre radius (base l t) (hidden l t)) (pderiv 3 Pb)| ≤ A := by
    rw [heq]
    obtain ⟨he0, he1⟩ := normPt_tests (T := T) (j := j) (c := c) (u := u) hQ hB.ne' P l.val t
    have htold := subblock_subset hjj ht
    obtain ⟨hv, hd⟩ := htests l.val l.property t htold
    refine ⟨?_, ?_⟩
    · change |eval _ (normPoly T j c u Q Bv P)| ≤ _
      rw [he0, div_mul_cancel₀ _ hApos.ne']
      exact hv
    · change |eval _ (pderiv 3 (normPoly T j c u Q Bv P))| ≤ _
      rw [he1, abs_mul, abs_inv, abs_of_pos hB]
      calc Bv⁻¹ * |eval (gx l.val t) (pderiv 3 P)| ≤ Bv⁻¹ * (U * Bv) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hB.le)
        _ = U := by field_simp
        _ ≤ A := hUle
  have hanchor : ‖centre + radius • base ⟨l0, hl0⟩ t0‖ ≤ A := by
    rw [← normBase_eq_center_add hradius.ne' Bv δfit (l0, t0)]
    exact (normBase_bound_of_chart hchart (hS l0 hl0).1 (subblock_subset hjj ht0)).trans hκA
  have hregular' : 4 * A ^ (-1 : ℝ) ≤
      |eval (comparisonCurvePoint centre radius (base ⟨l0, hl0⟩ t0) (hidden ⟨l0, hl0⟩ t0)) (pderiv 3 Pb)| := by
    rw [heq]
    obtain ⟨_, he1⟩ := normPt_tests (T := T) (j := j) (c := c) (u := u) hQ hB.ne' P l0 t0
    change _ ≤ |eval _ (pderiv 3 (normPoly T j c u Q Bv P))|
    rw [he1, abs_mul, abs_inv, abs_of_pos hB, Real.rpow_neg_one]
    have hn : 1 / U ≤ Bv⁻¹ * |eval (gx l0 t0) (pderiv 3 P)| := by
      calc
        1 / U = Bv⁻¹ * (Bv / U) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hregular (inv_nonneg.mpr hB.le)
    have hh : 4 * A⁻¹ ≤ 1 / U := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hApos hU]
      simpa only [one_mul] using hUA
    exact hh.trans hn
  have hmid : (ta + tb) / 2 = subMid T s₀ j jj := by dsimp only [ta, tb, subMid]; ring
  have hcont (l : S) : Continuous (fun t =>
      eval (comparisonCurvePoint centre radius (base l t) (hidden l t)) (pderiv 3 Pb)) := by
    simp only [heq]
    have he1 (t : ℝ) := (normPt_tests (T := T) (j := j) (c := c) (u := u) hQ hB.ne' P l.val t).2
    change Continuous (fun t => eval (normPt T j c u Q Bv l.val t)
      (pderiv 3 (normPoly T j c u Q Bv P)))
    simp only [he1]
    obtain ⟨a, b, hab⟩ := eval_pderiv_gx_affine hP l.val
    simp only [hab]
    fun_prop
  have hbits (l : S) :
      decide (0 ≤ eval (comparisonCurvePoint centre radius (base l ((ta + tb) / 2))
        (hidden l ((ta + tb) / 2))) (pderiv 3 Pb)) =
      decide (0 ≤ eval (comparisonCurvePoint centre radius (base ⟨l0, hl0⟩ ((ta + tb) / 2))
        (hidden ⟨l0, hl0⟩ ((ta + tb) / 2))) (pderiv 3 Pb)) := by
    simp only [heq]
    have he1 (l : ℕ × (Fin 6 → ℝ)) := (normPt_tests (T := T) (j := j) (c := c) (u := u) hQ hB.ne' P l ((ta + tb) / 2)).2
    change decide (0 ≤ eval (normPt T j c u Q Bv l.val ((ta + tb) / 2))
      (pderiv 3 (normPoly T j c u Q Bv P))) =
      decide (0 ≤ eval (normPt T j c u Q Bv l0 ((ta + tb) / 2))
        (pderiv 3 (normPoly T j c u Q Bv P)))
    have hsign (z : ℝ) : 0 ≤ Bv⁻¹ * z ↔ 0 ≤ z := by
      constructor
      · intro hz
        by_contra hn
        exact (not_le_of_gt (mul_neg_of_pos_of_neg (inv_pos.mpr hB) (lt_of_not_ge hn))) hz
      · exact fun hz => mul_nonneg (inv_nonneg.mpr hB.le) hz
    simp only [he1, hsign]
    rw [hmid]
    exact hbit l.val l.property
  obtain ⟨flat, F, hclass, hcert, hfits⟩ := hchoose A (U * δfit / A) hA hfit Pb hPb hcoeff
    centre base hidden ⟨l0, hl0⟩ ta tb t0 (by dsimp only [ta, tb]; apply div_le_div_of_nonneg_right (by linarith) (by positivity))
    ht0 hhalf hanchor (fun l t ht => (hbounds l t ht).1) (fun l t ht => (hbounds l t ht).2)
    hregular' hcont hbits
  let σ := eval (normPt T j c u Q Bv l0 t0) (pderiv 3 (selectedSheetTest flat Pb))
  have hcert' : NormalizedRootCertificate Pb flat F centre radius σ := by
    change NormalizedRootCertificate Pb flat F centre radius
      (eval (comparisonCurvePoint centre radius (base ⟨l0, hl0⟩ t0) (hidden ⟨l0, hl0⟩ t0))
        (pderiv 3 (selectedSheetTest flat Pb))) at hcert
    rw [heq] at hcert
    exact hcert
  refine ⟨flat, F, σ, hclass, hcert', rfl, ?_, ?_⟩
  · intro l hl t ht
    have hf := hfits ⟨l, hl⟩ t ht
    have he : (U * δfit / A) * A ^ ((Csheet : ℝ) + 2) = U * δfit * A ^ ((Csheet : ℝ) + 1) := by
      rw [show (Csheet : ℝ) + 2 = ((Csheet : ℝ) + 1) + 1 by ring, Real.rpow_add hApos, Real.rpow_one]
      field_simp
    simpa only [he] using hf
  · have hbounds0 := hbounds ⟨l0, hl0⟩ t0 ht0
    have hre : 4 * A ^ (-1 : ℝ) ≤ |eval (normPt T j c u Q Bv l0 t0) (pderiv 3 Pb)| := by
      simpa only [heq] using hregular'
    have hup : |eval (normPt T j c u Q Bv l0 t0) (pderiv 3 Pb)| ≤ A := by
      simpa only [heq] using hbounds0.2
    have hpoint : (Fin.snoc (fun z => normBase T j c u Q l0 t0 z)
        (Bv * gx l0 t0 3) : Fin 4 → ℝ) = normPt T j c u Q Bv l0 t0 := by
      rw [normBase_eq_init T j c u Q Bv l0 t0]
      exact snoc_init_eq _
    have hscale := normalized_initial_scale_bounds hPb flat hA hB hfit1
      (normBase T j c u Q l0 t0) (Bv * gx l0 t0 3) hclass
      (by simpa only [hpoint] using hre) (by simpa only [hpoint] using hup)
    simpa only [hpoint, σ, Pb] using hscale

section Certificate
variable {Csheet : ℕ} {A U δfit Bv : ℝ} {T j s₀ jj : ℕ}
  {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
  {P : MvPolynomial (Fin 4) ℝ} {k : Fin 2 → ℤ} {S : Set (ℕ × (Fin 6 → ℝ))}
  {l0 : ℕ × (Fin 6 → ℝ)} {t0 : ℝ} {flat : Bool} {Fs : RealSheet 2} {σ : ℝ}

/-- The certificate's roots give the physical root equation and signed derivative
window used by `group_step_entries_of_ac`. -/
theorem PacketLineSheetCertificate.physical_roots
    (hc : PacketLineSheetCertificate Csheet A U δfit T j s₀ jj c u Q Bv P k S l0 t0 flat Fs σ)
    (hA : 0 < A) (hQ : Q.det ≠ 0) (hB : 0 < Bv)
    (δobs : ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ)
    (hbase : ‖groupBase T j c u Q (subBoxCenter s₀ jj k) (A ^ (-(Csheet : ℝ)) / 128)
      (obs Bv δobs (l, t))‖ ≤ (1 : ℝ) / 2) :
    let x := groupBase T j c u Q (subBoxCenter s₀ jj k) (A ^ (-(Csheet : ℝ)) / 128)
      (obs Bv δobs (l, t))
    let w := (Fs.f (emb x)).re / Bv
    let sc := selectedSlopeFactor flat Bv * |σ|
    eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (selectedSheetTest flat P) = 0 ∧
      if decide (0 ≤ σ) then
        19 / 20 * sc ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat P)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat P)) ≤ 21 / 20 * sc
      else
        19 / 20 * sc ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat P)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat P)) ≤ 21 / 20 * sc := by
  exact (packet_root_of_normalized_certificate hQ hB P flat Fs (subBoxCenter s₀ jj k)
    (by positivity : 0 < A ^ (-(Csheet : ℝ)) / 128) σ hc.2.1 l t δobs
    (hbase.trans (by norm_num))).2

/-- Whole-block fits can be read at the terminal observation scale or at any
other bin scale, because the comparison base ignores the hidden bin. -/
theorem PacketLineSheetCertificate.fit_at_observation
    (hc : PacketLineSheetCertificate Csheet A U δfit T j s₀ jj c u Q Bv P k S l0 t0 flat Fs σ)
    (Bobs δobs : ℝ) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ S) {t : ℝ} (ht : t ∈ subBlock T s₀ j jj) :
    |Bv * gx l t 3 - (Fs.f (emb (groupBase T j c u Q (subBoxCenter s₀ jj k)
      (A ^ (-(Csheet : ℝ)) / 128) (obs Bobs δobs (l, t))))).re| ≤
      U * δfit * A ^ ((Csheet : ℝ) + 1) := by
  rw [groupBase_obs_independent T j c u Q (subBoxCenter s₀ jj k)
    (A ^ (-(Csheet : ℝ)) / 128) Bobs δobs Bv δfit (l, t)]
  exact hc.2.2.2.1 l hl t ht

end Certificate

end Submission.Obl.k4_clean_cover_graph_atlas
