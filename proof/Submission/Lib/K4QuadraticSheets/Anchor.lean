import Mathlib
import Submission.Lib.K4QuadraticSheets.LocalBranch

/-!
# Transport to a common anchor and back

The two deterministic halves of the representative step.

* **Forward** (`anchor_forward`): continue a source sheet and a witness sheet, which agree to
  `V` near the start `a` of a broken segment, to the anchor `c`.  The jets of the continued
  source sheet at the anchor are then within `A ^ C * V` of the jets of one of the two canonical
  local root branches of the witness test at the anchor.  These canonical branches depend only on
  the witness test and the anchor, so the witness determines the source's anchor jets up to two
  choices.
* **Return** (`anchor_return`): if the jets at the anchor of a sheet and of a representative
  branch agree to `V`, the representative test evaluated on the sheet is `≲ A ^ C * V` near the
  start of the segment.
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

local notation "E3" => EuclideanSpace ℂ (Fin 3)

/-- The canonical square root of the discriminant near a point `α`: the principal square root
rotated by the discriminant's value at `α`. -/
noncomputable def canonSqrt (P : MvPolynomial (Fin 4) ℂ) (α z : E3) : ℂ :=
  rotSqrt (qdisc P (fun j => α j)) ((qdisc P (fun j => α j)) ^ (1 / 2 : ℂ))
    (qdisc P (fun j => z j))

/-- The two canonical local root branches of a test near a point, indexed by a sign. -/
noncomputable def canonBranch (P : MvPolynomial (Fin 4) ℂ) (α : E3) (ε : Bool) (z : E3) : ℂ :=
  rootOf P (fun j => z j) (if ε then canonSqrt P α z else -canonSqrt P α z)

/-- Where the discriminant moves less than its size at `α`, the canonical square root is an
analytic square root of it. -/
theorem canonSqrt_spec {P : MvPolynomial (Fin 4) ℂ} {α : E3} {ρ : ℝ}
    (hpert : ∀ z ∈ Metric.ball α ρ,
      ‖qdisc P (fun j => z j) - qdisc P (fun j => α j)‖ < ‖qdisc P (fun j => α j)‖) :
    AnalyticOnNhd ℂ (canonSqrt P α) (Metric.ball α ρ) ∧
      ∀ z ∈ Metric.ball α ρ, canonSqrt P α z ^ 2 = qdisc P (fun j => z j) ∧
        qdisc P (fun j => z j) ≠ 0 := by
  by_cases hρ : ρ ≤ 0
  · rw [Metric.ball_eq_empty.mpr hρ]
    exact ⟨fun z hz => absurd hz (Set.notMem_empty z), fun z hz => absurd hz (Set.notMem_empty z)⟩
  rw [not_le] at hρ
  have ha0 : qdisc P (fun j => α j) ≠ 0 := by
    intro h0
    have := hpert α (Metric.mem_ball_self hρ)
    rw [h0, sub_zero, norm_zero] at this
    exact lt_irrefl _ this
  set lam := qdisc P (fun j => α j) with hlam
  have hμ2 : (lam ^ (1 / 2 : ℂ)) ^ 2 = lam := by
    have := Complex.cpow_nat_inv_pow lam (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [one_div]
    exact this
  have hmem : ∀ z ∈ Metric.ball α ρ, qdisc P (fun j => z j) / lam ∈ Complex.slitPlane := by
    intro z hz
    have heq : qdisc P (fun j => z j) / lam = 1 + (qdisc P (fun j => z j) - lam) / lam := by
      field_simp
      ring
    rw [heq]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr ha0)]
    exact hpert z hz
  refine ⟨analyticOnNhd_rotSqrt (fun z _ => analyticAt_qdisc P z) hmem, ?_⟩
  intro z hz
  refine ⟨rotSqrt_sq ha0 hμ2 _, ?_⟩
  intro h0
  have := hmem z hz
  rw [h0, zero_div] at this
  exact Complex.slitPlane_ne_zero this rfl

/-- The canonical branches are analytic simple sheets near `α`. -/
theorem canonBranch_spec {P : MvPolynomial (Fin 4) ℂ} (hP : P.totalDegree ≤ 2) (hP0 : P ≠ 0)
    {α : E3} {ρ : ℝ}
    (hpert : ∀ z ∈ Metric.ball α ρ,
      ‖qdisc P (fun j => z j) - qdisc P (fun j => α j)‖ < ‖qdisc P (fun j => α j)‖)
    (ε : Bool) :
    SimpleSheet P (canonBranch P α ε) (Metric.ball α ρ) ∧
      AnalyticOnNhd ℂ (canonBranch P α ε) (Metric.ball α ρ) := by
  obtain ⟨hSa, hS⟩ := canonSqrt_spec hpert
  cases ε
  · have hSa' : AnalyticOnNhd ℂ (fun z => -canonSqrt P α z) (Metric.ball α ρ) :=
      fun z hz => (hSa z hz).neg
    have hS' : ∀ z ∈ Metric.ball α ρ, (-canonSqrt P α z) ^ 2 = qdisc P (fun j => z j) ∧
        qdisc P (fun j => z j) ≠ 0 :=
      fun z hz => ⟨by rw [neg_sq]; exact (hS z hz).1, (hS z hz).2⟩
    have heq : canonBranch P α false = fun z => rootOf P (fun j => z j) (-canonSqrt P α z) := by
      funext z; simp [canonBranch]
    rw [heq]
    exact simpleSheet_rootOf hP hP0 hSa' hS'
  · have heq : canonBranch P α true = fun z => rootOf P (fun j => z j) (canonSqrt P α z) := by
      funext z; simp [canonBranch]
    rw [heq]
    exact simpleSheet_rootOf hP hP0 hSa hS

/-- Every simple sheet near `α` is one of the two canonical branches there. -/
theorem sheet_eq_canonBranch {P : MvPolynomial (Fin 4) ℂ} (hP : P.totalDegree ≤ 2)
    {α : E3} {ρ : ℝ} (hρ : 0 < ρ)
    (hpert : ∀ z ∈ Metric.ball α ρ,
      ‖qdisc P (fun j => z j) - qdisc P (fun j => α j)‖ < ‖qdisc P (fun j => α j)‖)
    {g : E3 → ℂ} (hgc : ContinuousOn g (Metric.ball α ρ))
    (hg : ∀ z ∈ Metric.ball α ρ,
      eval (Fin.snoc (fun j : Fin 3 => z j) (g z) : Fin 4 → ℂ) P = 0) :
    ∃ ε : Bool, ∀ z ∈ Metric.ball α ρ, g z = canonBranch P α ε z := by
  obtain ⟨hSa, hS⟩ := canonSqrt_spec hpert
  rcases root_branch_eq_rootOf hP (convex_ball α ρ).isPreconnected hSa.continuousOn
      (fun z hz => (hS z hz).1) (fun z hz => (hS z hz).2) hgc hg
      (Metric.mem_ball_self hρ) with h | h
  · exact ⟨true, fun z hz => by simpa [canonBranch] using h z hz⟩
  · exact ⟨false, fun z hz => by simpa [canonBranch] using h z hz⟩

/-- The ball of radius `A⁻¹` around the end of a broken segment lies in its `A⁻¹`-tube. -/
theorem ball_end_subset_tube (a b c : E3) (A : ℝ) :
    Metric.ball c (A⁻¹) ⊆ Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c) := by
  intro z hz
  rw [Metric.mem_thickening_iff]
  exact ⟨c, Or.inr (right_mem_segment ℝ b c), hz⟩

theorem ball_start_subset_tube (a b c : E3) (A : ℝ) :
    Metric.ball a (A⁻¹) ⊆ Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c) := by
  intro z hz
  rw [Metric.mem_thickening_iff]
  exact ⟨a, Or.inl (left_mem_segment ℝ a b), hz⟩

/-- **Forward transport to the anchor.**  Continue a source sheet and a witness sheet, given near
the start of a broken segment and agreeing there to `V`, along the segment.  At the anchor `c`
the jets of the continued source sheet are within `A ^ C * V` of the jets of one of the two
canonical branches of the witness test. -/
theorem anchor_forward (hC : ContInput) (s : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : E3,
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P P' : MvPolynomial (Fin 4) ℂ),
      P.totalDegree ≤ 2 → P ≠ 0 → P'.totalDegree ≤ 2 → P' ≠ 0 →
      ∀ (S S' : E3 → ℂ),
      AnalyticOnNhd ℂ S (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      (∀ z ∈ Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c),
        S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0) →
      AnalyticOnNhd ℂ S' (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      (∀ z ∈ Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c),
        S' z ^ 2 = qdisc P' (fun j => z j) ∧ qdisc P' (fun j => z j) ≠ 0) →
      (∀ z ∈ Metric.ball c (A⁻¹),
        ‖qdisc P' (fun j => z j) - qdisc P' (fun j => c j)‖ < ‖qdisc P' (fun j => c j)‖) →
      ∀ (f₀ f'₀ : E3 → ℂ),
      ContinuousOn f₀ (Metric.ball a (A⁻¹)) → ContinuousOn f'₀ (Metric.ball a (A⁻¹)) →
      (∀ z ∈ Metric.ball a (A⁻¹),
        eval (Fin.snoc (fun j : Fin 3 => z j) (f₀ z) : Fin 4 → ℂ) P = 0 ∧
        eval (Fin.snoc (fun j : Fin 3 => z j) (f'₀ z) : Fin 4 → ℂ) P' = 0) →
      ∀ V : ℝ, 0 ≤ V → (∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖f₀ z - f'₀ z‖ ≤ V) →
      ∃ f : E3 → ℂ, SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) ∧
        AnalyticOnNhd ℂ f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) ∧
        (∀ z ∈ Metric.ball a (A⁻¹), f z = f₀ z) ∧
        ∃ ε : Bool, ∀ j : ℕ, j ≤ q →
          ‖iteratedFDeriv ℂ j f c - iteratedFDeriv ℂ j (canonBranch P' c ε) c‖ ≤ A ^ C * V := by
  obtain ⟨q, C, hsq, hC0, hmain⟩ := cont_diff_forward hC s
  refine ⟨q, C, hsq, hC0, ?_⟩
  intro A hA a b c ha hb hc P P' hP hP0 hP' hP'0 S S' hSa hS hS'a hS' hpert f₀ f'₀ hf₀c hf'₀c
    hroots V hV hclose
  set U := Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c) with hU
  have hAinv : 0 < A⁻¹ := inv_pos.mpr (by linarith)
  have hBa : Metric.ball a (A⁻¹) ⊆ U := ball_start_subset_tube a b c A
  have hBc : Metric.ball c (A⁻¹) ⊆ U := ball_end_subset_tube a b c A
  -- continue both local branches along the tube
  obtain ⟨f, hfs, hfa, hff₀⟩ := exists_continued_sheet hP hP0 hSa hS hBa
    (convex_ball a _).isPreconnected (Metric.mem_ball_self hAinv) hf₀c
    (fun z hz => (hroots z hz).1)
  obtain ⟨f', hf's, hf'a, hf'f'₀⟩ := exists_continued_sheet hP' hP'0 hS'a hS' hBa
    (convex_ball a _).isPreconnected (Metric.mem_ball_self hAinv) hf'₀c
    (fun z hz => (hroots z hz).2)
  refine ⟨f, hfs, hfa, hff₀, ?_⟩
  -- the continued sheets still agree near the start
  have hsmall : (8 * A)⁻¹ < A⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by linarith)]
    linarith
  have hclose' : ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖f z - f' z‖ ≤ V := by
    intro z hz
    have hz' : z ∈ Metric.ball a (A⁻¹) :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hsmall)
    rw [hff₀ z hz', hf'f'₀ z hz']
    exact hclose z hz
  have hjets := ((hmain A hA a b c ha hb hc P P' f f' hfs hf's V hV).1 hclose').2
  -- near the anchor, the continued witness sheet is a canonical branch
  obtain ⟨ε, hε⟩ := sheet_eq_canonBranch hP' hAinv hpert
    (hf's.2.2.1.continuousOn.mono hBc) (fun z hz => (hf's.2.2.2 z (hBc hz)).1)
  refine ⟨ε, fun j hj => ?_⟩
  have hjet_eq : iteratedFDeriv ℂ j f' c = iteratedFDeriv ℂ j (canonBranch P' c ε) c :=
    iteratedFDeriv_eq_of_eqOn_ball hAinv hε j
  have hcU : c ∈ U := hBc (Metric.mem_ball_self hAinv)
  have hsub : iteratedFDeriv ℂ j (fun z => f z - f' z) c =
      iteratedFDeriv ℂ j f c - iteratedFDeriv ℂ j f' c :=
    iteratedFDeriv_sub_apply (hfa c hcU).contDiffAt (hf'a c hcU).contDiffAt
  rw [← hjet_eq, ← hsub]
  exact hjets j hj

end Submission.Lib.K4QuadraticSheets

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

local notation "E3" => EuclideanSpace ℂ (Fin 3)

/-- The difference of a quadratic test at two hidden values. -/
theorem eval_snoc_sub_eval_snoc {P : MvPolynomial (Fin 4) ℂ} (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℂ) (w₁ w₂ : ℂ) :
    eval (Fin.snoc z w₁ : Fin 4 → ℂ) P - eval (Fin.snoc z w₂ : Fin 4 → ℂ) P =
      (w₁ - w₂) * (eval (Fin.snoc z w₂ : Fin 4 → ℂ) (pderiv (Fin.last 3) P) +
        qc P / 2 * (w₁ - w₂)) := by
  rw [eval_snoc_quadratic P hP, eval_snoc_quadratic P hP, eval_snoc_pderiv P hP]
  ring

theorem tube_symm (a b c : E3) (r : ℝ) :
    Metric.thickening r (segment ℝ c b ∪ segment ℝ b a) =
      Metric.thickening r (segment ℝ a b ∪ segment ℝ b c) := by
  rw [segment_symm ℝ c b, segment_symm ℝ b a, Set.union_comm]

theorem tube_point (c : E3) (r : ℝ) :
    Metric.thickening r (segment ℝ c c ∪ segment ℝ c c) = Metric.ball c r := by
  rw [Set.union_self, segment_same, Metric.thickening_singleton]

/-- **Return from the anchor.**  If the jets at the anchor `c` of a sheet `f` (continued along
the broken segment) and of a representative branch `fr` agree to `V`, then the representative test
evaluated on the sheet is `≤ A ^ C * (A ^ C * V) * (K + |ĉ| A ^ C V / 2)` near the start `a`, where
`K` bounds the representative's hidden derivative on its own branch near the anchor. -/
theorem anchor_return (hC : ContInput) (s : ℕ) :
    ∃ q : ℕ, ∃ C₁ C₂ : ℝ, s ≤ q ∧ 0 < C₁ ∧ 0 < C₂ ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : E3,
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P Pr : MvPolynomial (Fin 4) ℂ),
      Pr.totalDegree ≤ 2 → ∀ (f fr : E3 → ℂ),
      SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      AnalyticOnNhd ℂ f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      SimpleSheet Pr fr (Metric.ball c (A⁻¹)) → AnalyticOnNhd ℂ fr (Metric.ball c (A⁻¹)) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹),
        ‖eval (Fin.snoc (fun j : Fin 3 => z j) (fr z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr)‖ ≤
          K) →
      ∀ V : ℝ, 0 ≤ V →
      (∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j f c - iteratedFDeriv ℂ j fr c‖ ≤ V) →
      ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹),
        ‖eval (Fin.snoc (fun j : Fin 3 => z j) (f z) : Fin 4 → ℂ) Pr‖ ≤
          A ^ C₂ * ((A ^ C₁ * V) * (K + ‖qc Pr‖ / 2 * (A ^ C₁ * V))) := by
  obtain ⟨q, C₁, hsq, hC₁, hmain₁⟩ := cont_diff_forward hC s
  obtain ⟨_q₂, C₂, hC₂, hmain₂⟩ := cont_eval hC 2
  refine ⟨q, C₁, C₂, hsq, hC₁, hC₂, ?_⟩
  intro A hA a b c ha hb hc P Pr hPr f fr hfs hfa hfrs hfra K hK hKb V hV hjets
  have hAinv : 0 < A⁻¹ := inv_pos.mpr (by linarith)
  have hBc : Metric.ball c (A⁻¹) ⊆
      Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c) := ball_end_subset_tube a b c A
  have hcU := hBc (Metric.mem_ball_self hAinv)
  -- step 1: close jets give a close difference on a ball around the anchor
  have hfs' : SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ c c ∪ segment ℝ c c)) := by
    rw [tube_point]; exact hfs.mono hBc
  have hfrs' : SimpleSheet Pr fr (Metric.thickening (A⁻¹) (segment ℝ c c ∪ segment ℝ c c)) := by
    rw [tube_point]; exact hfrs
  have hdiff := (hmain₁ A hA c c c hc hc hc P Pr f fr hfs' hfrs' V hV).2 (by
    intro j hj
    have hsub : iteratedFDeriv ℂ j (fun z => f z - fr z) c =
        iteratedFDeriv ℂ j f c - iteratedFDeriv ℂ j fr c :=
      iteratedFDeriv_sub_apply (hfa c hcU).contDiffAt
        (hfra c (Metric.mem_ball_self hAinv)).contDiffAt
    rw [hsub]
    exact hjets j hj)
  -- step 2: the representative test on the sheet near the anchor
  have hsmall : (8 * A)⁻¹ < A⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by linarith)]
    linarith
  have hnear : ∀ z ∈ Metric.closedBall c ((8 * A)⁻¹),
      ‖eval (Fin.snoc (fun j : Fin 3 => z j) (f z) : Fin 4 → ℂ) Pr‖ ≤
        (A ^ C₁ * V) * (K + ‖qc Pr‖ / 2 * (A ^ C₁ * V)) := by
    intro z hz
    have hzB : z ∈ Metric.ball c (A⁻¹) :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hsmall)
    have h0 := (hfrs.2.2.2 z hzB).1
    have hid := eval_snoc_sub_eval_snoc hPr (fun j : Fin 3 => z j) (f z) (fr z)
    rw [h0, sub_zero] at hid
    rw [hid, norm_mul]
    have hd := hdiff z hz
    have hd0 : 0 ≤ A ^ C₁ * V := mul_nonneg (Real.rpow_nonneg (by linarith) _) hV
    apply mul_le_mul hd _ (norm_nonneg _) hd0
    calc ‖eval (Fin.snoc (fun j : Fin 3 => z j) (fr z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr) +
          qc Pr / 2 * (f z - fr z)‖
        ≤ ‖eval (Fin.snoc (fun j : Fin 3 => z j) (fr z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr)‖ +
          ‖qc Pr / 2 * (f z - fr z)‖ := norm_add_le _ _
      _ ≤ K + ‖qc Pr‖ / 2 * (A ^ C₁ * V) := by
          gcongr
          · exact hKb z hz
          · rw [norm_mul, norm_div]
            simp only [Complex.norm_ofNat]
            exact mul_le_mul_of_nonneg_left hd (by positivity)
  -- step 3: transport the evaluation back along the reversed segment
  have hfs'' : SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ c b ∪ segment ℝ b a)) := by
    rw [tube_symm]; exact hfs
  have hV₂ : 0 ≤ (A ^ C₁ * V) * (K + ‖qc Pr‖ / 2 * (A ^ C₁ * V)) := by
    have hd0 : 0 ≤ A ^ C₁ * V := mul_nonneg (Real.rpow_nonneg (by linarith) _) hV
    positivity
  have hback := ((hmain₂ A hA c b a hc hb ha P Pr f hfs'' hPr _ hV₂).1 hnear).1
  exact hback

end Submission.Lib.K4QuadraticSheets

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

local notation "E3" => EuclideanSpace ℂ (Fin 3)

/-- **Return of the hidden derivative.**  Under the hypotheses of `anchor_return`, the hidden
derivative of the representative test on the sheet is `≤ A ^ C₂ * (K + |ĉ| A ^ C₁ V)` near the
start of the segment. -/
theorem anchor_return_deriv (hC : ContInput) (s : ℕ) :
    ∃ q : ℕ, ∃ C₁ C₂ : ℝ, s ≤ q ∧ 0 < C₁ ∧ 0 < C₂ ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : E3,
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P Pr : MvPolynomial (Fin 4) ℂ),
      Pr.totalDegree ≤ 2 → ∀ (f fr : E3 → ℂ),
      SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      AnalyticOnNhd ℂ f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      SimpleSheet Pr fr (Metric.ball c (A⁻¹)) → AnalyticOnNhd ℂ fr (Metric.ball c (A⁻¹)) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹),
        ‖eval (Fin.snoc (fun j : Fin 3 => z j) (fr z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr)‖ ≤
          K) →
      ∀ V : ℝ, 0 ≤ V →
      (∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j f c - iteratedFDeriv ℂ j fr c‖ ≤ V) →
      ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹),
        ‖eval (Fin.snoc (fun j : Fin 3 => z j) (f z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr)‖ ≤
          A ^ C₂ * (K + ‖qc Pr‖ * (A ^ C₁ * V)) := by
  obtain ⟨q, C₁, hsq, hC₁, hmain₁⟩ := cont_diff_forward hC s
  obtain ⟨_q₂, C₂, hC₂, hmain₂⟩ := cont_eval hC 2
  refine ⟨q, C₁, C₂, hsq, hC₁, hC₂, ?_⟩
  intro A hA a b c ha hb hc P Pr hPr f fr hfs hfa hfrs hfra K hK hKb V hV hjets
  have hAinv : 0 < A⁻¹ := inv_pos.mpr (by linarith)
  have hBc : Metric.ball c (A⁻¹) ⊆
      Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c) := ball_end_subset_tube a b c A
  have hcU := hBc (Metric.mem_ball_self hAinv)
  have hfs' : SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ c c ∪ segment ℝ c c)) := by
    rw [tube_point]; exact hfs.mono hBc
  have hfrs' : SimpleSheet Pr fr (Metric.thickening (A⁻¹) (segment ℝ c c ∪ segment ℝ c c)) := by
    rw [tube_point]; exact hfrs
  have hdiff := (hmain₁ A hA c c c hc hc hc P Pr f fr hfs' hfrs' V hV).2 (by
    intro j hj
    have hsub : iteratedFDeriv ℂ j (fun z => f z - fr z) c =
        iteratedFDeriv ℂ j f c - iteratedFDeriv ℂ j fr c :=
      iteratedFDeriv_sub_apply (hfa c hcU).contDiffAt
        (hfra c (Metric.mem_ball_self hAinv)).contDiffAt
    rw [hsub]
    exact hjets j hj)
  have hnear : ∀ z ∈ Metric.closedBall c ((8 * A)⁻¹),
      ‖eval (Fin.snoc (fun j : Fin 3 => z j) (f z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr)‖ ≤
        K + ‖qc Pr‖ * (A ^ C₁ * V) := by
    intro z hz
    have hid : eval (Fin.snoc (fun j : Fin 3 => z j) (f z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr) =
        eval (Fin.snoc (fun j : Fin 3 => z j) (fr z) : Fin 4 → ℂ) (pderiv (Fin.last 3) Pr) +
          qc Pr * (f z - fr z) := by
      rw [eval_snoc_pderiv Pr hPr, eval_snoc_pderiv Pr hPr]
      ring
    rw [hid]
    calc _ ≤ ‖eval (Fin.snoc (fun j : Fin 3 => z j) (fr z) : Fin 4 → ℂ)
          (pderiv (Fin.last 3) Pr)‖ + ‖qc Pr * (f z - fr z)‖ := norm_add_le _ _
      _ ≤ K + ‖qc Pr‖ * (A ^ C₁ * V) := by
          gcongr
          · exact hKb z hz
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hdiff z hz) (norm_nonneg _)
  have hfs'' : SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ c b ∪ segment ℝ b a)) := by
    rw [tube_symm]; exact hfs
  have hdeg : (pderiv (Fin.last 3) Pr).totalDegree ≤ 2 :=
    (totalDegree_pderiv_le' Pr _ (d := 1) hPr).trans (by norm_num)
  have hV₂ : 0 ≤ K + ‖qc Pr‖ * (A ^ C₁ * V) := by
    have hd0 : 0 ≤ A ^ C₁ * V := mul_nonneg (Real.rpow_nonneg (by linarith) _) hV
    positivity
  exact ((hmain₂ A hA c b a hc hb ha P (pderiv (Fin.last 3) Pr) f hfs'' hdeg _ hV₂).1 hnear).1

end Submission.Lib.K4QuadraticSheets
