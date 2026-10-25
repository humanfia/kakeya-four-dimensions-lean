import Submission.Obl.k4_matching_homogeneous_records.Dyadic

namespace Submission.Obl.k4_matching_homogeneous_records

open Set

abbrev StageType (J : ℕ) := ℤ × (Fin (J + 1) → ℤ × ℤ)
abbrev HistoryType (q J : ℕ) := Fin (q + 1) → StageType J

noncomputable def stageFromCell {n₁ n₂ : ℕ} (J : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (v : ℕ)
    (p : (Fin n₁ × Fin n₂) × ℤ) : StageType J :=
  (p.2, fun j =>
    (Int.floor (w v j * iteratedDeriv j (f₁ p.1.1) (((p.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ h v)),
     Int.floor (w v j * iteratedDeriv j (f₂ p.1.2) (((p.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ h v))))

noncomputable def history {n₁ n₂ : ℕ} (q J : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k : ℕ)
    (p : (Fin n₁ × Fin n₂) × ℝ) : HistoryType q J :=
  fun v => if v.val ≤ k then
    stageFromCell J f₁ f₂ h w v (p.1, Int.floor (p.2 * (2 : ℝ) ^ h v)) else (0, fun _ => (0, 0))

noncomputable def recordCode {n₁ n₂ : ℕ} (q J : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k : ℕ)
    (p : (Fin n₁ × Fin n₂) × ℝ) : ℕ :=
  Encodable.encode (history q J f₁ f₂ h w k p)

lemma measurable_recordCode {n₁ n₂ : ℕ} (q J : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k : ℕ) :
    Measurable (recordCode q J f₁ f₂ h w k) := by
  unfold recordCode
  apply (measurable_of_countable Encodable.encode).comp
  apply Measurable.of_eval
  intro v
  by_cases hv : v.val ≤ k
  · simp only [history, ite_eq_left hv]
    exact (measurable_of_countable (stageFromCell J f₁ f₂ h w v)).comp
      (measurable_fst.prodMk (Int.measurable_floor.comp (measurable_snd.mul_const _)))
  · simpa only [history, ite_eq_right hv] using
      (measurable_const : Measurable (fun _ : (Fin n₁ × Fin n₂) × ℝ => ((0, fun _ : Fin (J + 1) => (0, 0)) : StageType J)))

lemma recordCode_eq_iff {n₁ n₂ : ℕ} (q J : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) {k : ℕ} (hk : k ≤ q)
    (x y : (Fin n₁ × Fin n₂) × ℝ) :
    recordCode q J f₁ f₂ h w k x = recordCode q J f₁ f₂ h w k y ↔
      ∀ v : ℕ, v ≤ k →
        Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧
        ∀ j : ℕ, j ≤ J →
          Int.floor (w v j * iteratedDeriv j (f₁ x.1.1) (dyadicCenter (h v) x.2)) =
            Int.floor (w v j * iteratedDeriv j (f₁ y.1.1) (dyadicCenter (h v) y.2)) ∧
          Int.floor (w v j * iteratedDeriv j (f₂ x.1.2) (dyadicCenter (h v) x.2)) =
            Int.floor (w v j * iteratedDeriv j (f₂ y.1.2) (dyadicCenter (h v) y.2)) := by
  unfold recordCode
  rw [Encodable.encode_inj]
  constructor
  · intro he v hv
    have hev := congrFun he (⟨v, by omega⟩ : Fin (q + 1))
    simp only [history, ite_eq_left hv] at hev
    refine ⟨congrArg Prod.fst hev, ?_⟩
    intro j hj
    have he' := congrFun (congrArg Prod.snd hev) (⟨j, by omega⟩ : Fin (J + 1))
    exact ⟨congrArg Prod.fst he', congrArg Prod.snd he'⟩
  · intro he
    funext v
    by_cases hv : v.val ≤ k
    · simp only [history, ite_eq_left hv]
      apply Prod.ext (he v hv).1
      funext j
      exact Prod.ext ((he v hv).2 j (by omega)).1 ((he v hv).2 j (by omega)).2
    · simp only [history, ite_eq_right hv]

lemma recordCode_nested {n₁ n₂ : ℕ} (q J : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ q) (x y : (Fin n₁ × Fin n₂) × ℝ)
    (he : recordCode q J f₁ f₂ h w b x = recordCode q J f₁ f₂ h w b y) :
    recordCode q J f₁ f₂ h w a x = recordCode q J f₁ f₂ h w a y := by
  apply (recordCode_eq_iff q J f₁ f₂ h w (hab.trans hb) x y).2
  intro v hv
  exact (recordCode_eq_iff q J f₁ f₂ h w hb x y).1 he v (hv.trans hab)

lemma floor_dyadic_refinement {a b : ℕ} (hab : a ≤ b) (t : ℝ) :
    Int.floor (t * (2 : ℝ) ^ a) =
      Int.floor (t * (2 : ℝ) ^ b) / (2 : ℤ) ^ (b - a) := by
  have he : t * (2 : ℝ) ^ a = t * (2 : ℝ) ^ b / ((2 ^ (b - a) : ℕ) : ℝ) := by
    have hb : b = a + (b - a) := by omega
    conv_rhs => arg 1; arg 2; rw [hb, pow_add]
    push_cast
    field_simp
  rw [he, Int.floor_div_natCast]
  norm_cast

lemma floor_dyadic_eq_of_finer_eq {a b : ℕ} (hab : a ≤ b) {s t : ℝ}
    (he : Int.floor (s * (2 : ℝ) ^ b) = Int.floor (t * (2 : ℝ) ^ b)) :
    Int.floor (s * (2 : ℝ) ^ a) = Int.floor (t * (2 : ℝ) ^ a) := by
  rw [floor_dyadic_refinement hab, floor_dyadic_refinement hab, he]

end Submission.Obl.k4_matching_homogeneous_records
