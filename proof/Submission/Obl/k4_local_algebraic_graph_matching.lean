import Mathlib
import ChallengeDeps
import Submission.Obl.k4_algebraic_real_jet_comparison
import Submission.Obl.k4_original_prior_line_extraction
set_option linter.unusedVariables false

/-!
# `Submission.k4_local_algebraic_graph_matching`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_local_algebraic_graph_matching`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_local_algebraic_graph_matching/`
belong to this obligation.
-/

theorem Submission.k4_local_algebraic_graph_matching : ((∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0)) → (∀ D : ℕ, ∀ d₀ : ℝ, 0 ≤ d₀ → d₀ < 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ → ∀ n₁ n₂ : ℕ, ∀ (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ) (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (P₁ : Fin n₁ → MvPolynomial (Fin 4) ℂ) (P₂ : Fin n₂ → MvPolynomial (Fin 4) ℂ) (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))), (fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) => (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) → (∀ i, P₁ i ≠ 0 ∧ (P₁ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₁ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₁ i z)) (P₁ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₁ i (emb x)).im = 0 ∧ ‖f₁ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, P₂ i ≠ 0 ∧ (P₂ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₂ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₂ i z)) (P₂ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₂ i (emb x)).im = 0 ∧ ‖f₂ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, 0 ≤ π₁ i) → (∀ i, 0 ≤ π₂ i) → (∑ i, π₁ i) = 1 → (∑ i, π₂ i) = 1 → ENNReal.ofReal (R ^ (-ε)) ≤ μ Set.univ → μ Set.univ ≤ 1 → (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₁ i) * MeasureTheory.volume U) → (∀ (i : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₂ i) * MeasureTheory.volume U) → ¬ μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε) ∧ ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧ M * R ^ (-ε) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}ᶜ = 0) (fun x => WithLp.toLp 2 (fun i => (x i : ℂ)))) := by
  classical
  intro hMatch D d₀ hd₀ hd₁
  obtain ⟨K, hK, V, hV, c, hc, B, hB, hjets⟩ :=
    Submission.k4_algebraic_real_jet_comparison D
  obtain ⟨η, hη, N₀, hN₀, hmatch⟩ :=
    hMatch K (K + 1) hK (Nat.lt_succ_self K) d₀ hd₀ hd₁
  obtain ⟨ε₀, hε₀, R₀, hR₀, hextract⟩ :=
    Submission.k4_original_prior_line_extraction V K (K + 1) hV hK
      (Nat.lt_succ_self K) (fun m => B m * 2) c η
      (fun m _ => mul_pos (hB m) (by norm_num)) hc hη
  refine ⟨min ε₀ η, lt_min hε₀ hη, max R₀ N₀,
    hR₀.trans (le_max_left _ _), ?_⟩
  intro R M ε hR hM hε hεle n₁ n₂ f₁ f₂ P₁ P₂ f₀ π₁ π₂ μ
  dsimp only
  intro hn₁ hn₂ hf₁ hf₂ hπ₁ hπ₂ hsum₁ hsum₂ hmass₁ hmass₂ hmarg₁ hmarg₂ hgood
  have hε₀' : ε ≤ ε₀ := hεle.trans (min_le_left _ _)
  have hεη : ε ≤ η := hεle.trans (min_le_right _ _)
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans hR
  have hRN₀ : N₀ ≤ R := (le_max_right _ _).trans hR
  have hRtwo : 2 ≤ R := hR₀.trans hRR₀
  have hRone : 1 ≤ R := (by norm_num : (1 : ℝ) ≤ 2).trans hRtwo
  have hn₁zero : n₁ ≠ 0 := by
    intro hn
    subst n₁
    simp at hsum₁
  let i₀ : Fin n₁ := ⟨0, Nat.pos_of_ne_zero hn₁zero⟩
  let emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) :=
    fun x => WithLp.toLp 2 (fun i => (x i : ℂ))
  let a := f₁ i₀
  let F₁ : Fin n₁ → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun i x => (f₁ i (emb x) - a (emb x)).re
  let F₂ : Fin n₂ → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun i x => (f₂ i (emb x) - a (emb x)).re
  have ha := hf₁ i₀
  have jet₁ := fun i : Fin n₁ => hjets (f₁ i) a (P₁ i) (P₁ i₀)
    (hf₁ i).1 ha.1 (hf₁ i).2.1 ha.2.1 (hf₁ i).2.2.1 ha.2.2.1
    (hf₁ i).2.2.2.1 ha.2.2.2.1
    (fun x hx => ⟨((hf₁ i).2.2.2.2 x hx).1, (ha.2.2.2.2 x hx).1⟩)
  have jet₂ := fun i : Fin n₂ => hjets (f₂ i) a (P₂ i) (P₁ i₀)
    (hf₂ i).1 ha.1 (hf₂ i).2.1 ha.2.1 (hf₂ i).2.2.1 ha.2.2.1
    (hf₂ i).2.2.2.1 ha.2.2.2.1
    (fun x hx => ⟨((hf₂ i).2.2.2.2 x hx).1, (ha.2.2.2.2 x hx).1⟩)
  have hA : 0 < 2 * (M * R ^ ε) :=
    mul_pos (by norm_num) (mul_pos hM (Real.rpow_pos_of_pos (by linarith) ε))
  have bound₁ (i : Fin n₁) (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) :
      ‖f₁ i (emb x) - a (emb x)‖ ≤ 2 * (M * R ^ ε) := by
    calc
      ‖f₁ i (emb x) - a (emb x)‖ =
          ‖(f₁ i (emb x) - f₀ x) - (a (emb x) - f₀ x)‖ := by congr 1; ring
      _ ≤ ‖f₁ i (emb x) - f₀ x‖ + ‖a (emb x) - f₀ x‖ := norm_sub_le _ _
      _ ≤ 2 * (M * R ^ ε) := by
        have h₁ := ((hf₁ i).2.2.2.2 x hx).2
        have h₂ := (ha.2.2.2.2 x hx).2
        linarith
  have bound₂ (i : Fin n₂) (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) :
      ‖f₂ i (emb x) - a (emb x)‖ ≤ 2 * (M * R ^ ε) := by
    calc
      ‖f₂ i (emb x) - a (emb x)‖ =
          ‖(f₂ i (emb x) - f₀ x) - (a (emb x) - f₀ x)‖ := by congr 1; ring
      _ ≤ ‖f₂ i (emb x) - f₀ x‖ + ‖a (emb x) - f₀ x‖ := norm_sub_le _ _
      _ ≤ 2 * (M * R ^ ε) := by
        have h₁ := ((hf₂ i).2.2.2.2 x hx).2
        have h₂ := (ha.2.2.2.2 x hx).2
        linarith
  have hdiff (i : Fin n₁) (j : Fin n₂) (x v : EuclideanSpace ℝ (Fin 3)) :
      (fun t : ℝ => F₁ i (x + t • v) - F₂ j (x + t • v)) =
        (fun t : ℝ => (f₁ i (emb (x + t • v)) - f₂ j (emb (x + t • v))).re) := by
    funext t
    dsimp only [F₁, F₂]
    simp only [Complex.sub_re]
    ring
  have hgood' : μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
      |F₁ p.1.1 p.2 - F₂ p.1.2 p.2| ≤ M * R ^ (-1 + ε) ∧
      c * (M * R ^ (-ε)) ≤ ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1),
        |iteratedDeriv j (fun t : ℝ =>
          F₁ p.1.1 (p.2 + t • v) - F₂ p.1.2 (p.2 + t • v)) 0|}ᶜ = 0 := by
    apply MeasureTheory.measure_mono_null (Set.compl_subset_compl.mpr ?_) hgood
    rintro ⟨⟨i, j⟩, x⟩ ⟨hx, hclose, y, hy, hsep⟩
    refine ⟨hx, ?_, ?_⟩
    · change |F₁ i x - F₂ j x| ≤ _
      have he : F₁ i x - F₂ j x = (f₁ i (emb x) - f₂ j (emb x)).re := by
        simpa only [zero_smul, add_zero] using congrFun (hdiff i j x 0) 0
      rw [he]
      exact (Complex.abs_re_le_norm _).trans hclose
    · have hp := hjets (f₁ i) (f₂ j) (P₁ i) (P₂ j)
        (hf₁ i).1 (hf₂ j).1 (hf₁ i).2.1 (hf₂ j).2.1
        (hf₁ i).2.2.1 (hf₂ j).2.2.1 (hf₁ i).2.2.2.1 (hf₂ j).2.2.2.1
        (fun u hu => ⟨((hf₁ i).2.2.2.2 u hu).1, ((hf₂ j).2.2.2.2 u hu).1⟩)
      change c * (M * R ^ (-ε)) ≤ _
      simp_rw [hdiff i j x]
      exact (mul_le_mul_of_nonneg_left hsep hc.le).trans (hp.2.2.2 x y hx hy)
  obtain ⟨g₁, g₂, ν, hg₁, hg₂, hder₁, hder₂, hν, hmar₁, hmar₂, hbad⟩ :=
    hextract R M ε hRR₀ hM hε hε₀' n₁ n₂ F₁ F₂ π₁ π₂ μ
      (fun i v hv x hx => ((jet₁ i).1 v hv x hx).of_le le_top)
      (fun i v hv x hx => ((jet₂ i).1 v hv x hx).of_le le_top)
      (fun i v hv m _ => (jet₁ i).2.1 v hv m)
      (fun i v hv m _ => (jet₂ i).2.1 v hv m)
      (fun i v hv m _ x hx => by
        simpa only [mul_assoc] using (jet₁ i).2.2.1 _ hA (bound₁ i) v hv m x hx)
      (fun i v hv m _ x hx => by
        simpa only [mul_assoc] using (jet₂ i).2.2.1 _ hA (bound₂ i) v hv m x hx)
      hπ₁ hπ₂ hsum₁ hsum₂ hmass₁ hmass₂ hmarg₁ hmarg₂ hgood'
  have hsize₁ : (n₁ : ℝ) ≤ R ^ (d₀ + η) :=
    hn₁.trans (Real.rpow_le_rpow_of_exponent_le hRone (add_le_add le_rfl hεη))
  have hsize₂ : (n₂ : ℝ) ≤ R ^ (d₀ + η) :=
    hn₂.trans (Real.rpow_le_rpow_of_exponent_le hRone (add_le_add le_rfl hεη))
  exact hmatch R hRN₀ n₁ n₂ g₁ g₂ π₁ π₂ ν hsize₁ hsize₂
    hg₁ hg₂ hder₁ hder₂ hπ₁ hπ₂ hsum₁ hsum₂ hν hmar₁ hmar₂ hbad
