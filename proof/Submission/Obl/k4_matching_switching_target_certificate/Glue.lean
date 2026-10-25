-- Adapted from this LOT tree, o070/x0242 split s028, Glue.lean.
import Submission.Obl.k4_matching_switching_target_certificate.Interfaces
import Submission.Obl.k4_matching_switching_target_certificate.Records

namespace Submission.Obl.k4_matching_switching_target_certificate

/-- Combine deterministic path covers with abstract switching domination. -/
theorem assemble (hgeometry : GeometricCoverStatement)
    (hprobability : AbstractSwitchingStatement) :
∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → ∀ β : ℕ → ℝ, ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)) → (fun r : ℝ → ℝ => (fun l : ℕ → ℝ → ℝ => ∀ γ : ℝ, 0 < γ → ∀ q : ℕ, 1 ≤ q → 4 ≤ γ * (q : ℝ) → ∀ (k v z : ℕ) (u : ℕ → ℝ), (k + 6 * (J + 1) ≤ q ∧ 1 ≤ v ∧ v ≤ J ∧ β (v) < 2 ∧ z ≤ k ∧ γ ≤ (z : ℝ) / (q : ℝ) ∧ ∀ x ∈ Set.Icc ((z : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)), r x = (x - β (v)) / (v : ℝ) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ v → (x - β j) / (j : ℝ) < r x) ∧ (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧ (∀ i : ℕ, 1 ≤ i → v + i ≤ J → γ ≤ l (v + i) x + (i : ℝ) * r x - β (v))) → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R : ℝ, 2 ≤ R ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N : ℝ, R ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)) (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)), (fun c : ℕ → ℝ → ℝ => (n₁ : ℝ) ≤ N ^ (d + ε) ∧ (n₂ : ℝ) ≤ N ^ (d + ε) ∧ (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧ (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧ (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧ (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₁ i) * MeasureTheory.volume E) ∧ (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₂ i) * MeasureTheory.volume E) ∧ MeasurableSet S ∧ μ Sᶜ = 0 ∧ (∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ J → |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧ (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b) ∧ (∀ k : ℕ, k ≤ q → N ^ (r ((k : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h k ∧ (2 : ℝ) ^ h k ≤ 2 * N ^ (r ((k : ℝ) / (q : ℝ)))) ∧ (∀ k : ℕ, k ≤ q → Measurable (F k) ∧ (F k '' S).Finite) ∧ (∀ k : ℕ, k ≤ q → ∀ x ∈ S, ∀ y ∈ S, F k x = F k y ↔ ∀ v : ℕ, v ≤ k → Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧ ∀ j : ℕ, j ≤ J → Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c v x.2)) = Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c v y.2)) ∧ Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c v x.2)) = Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c v y.2))) ∧ (∀ k : ℕ, k ≤ q → ((F k '' S).ncard : ℝ) ≤ N ^ (u k + ε)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S, ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε))) (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v) → ((fun Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ => (fun P : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => μ {x | x ∈ S ∧ N ^ θ * P k x < P (k + 6 * (J + 1)) x} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (J + 10))) (fun k (x : ((Fin n₁ × Fin n₂) × ℝ)) => (μ {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x}).toReal / (μ {y | y ∈ S ∧ F k y = F k x}).toReal)) ((fun c : ℕ → ℝ → ℝ => fun x : ((Fin n₁ × Fin n₂) × ℝ) => (Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₁ x.1.1) (c z x.2)), Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₂ x.1.2) (c z x.2)))) (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v))) → (fun Δ : ℝ => ∃ (K : ℝ) (n : ℕ) (w : Fin n → ℝ) (U : Fin n → Fin (v + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin v → ℝ))), 2 ≤ K ∧ K ≤ N ^ κ ∧ (∀ i : Fin n, 0 ≤ w i) ∧ (∑ i : Fin n, w i) ≤ 1 ∧ (∀ (i : Fin n) (p : Fin (v + 1)), |U i p| ≤ K) ∧ |s₀| ≤ 1 ∧ (∀ (i : Fin n) (p : Fin v), K⁻¹ ≤ |U i p.succ - U i p.castSucc|) ∧ MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (K * N ^ (Δ - (1 / (v : ℝ) + ((v : ℝ) + 1) / 2) / (q : ℝ))) ∧ 1 / 4 ≤ K * N ^ (((v : ℝ) + 1) * θ) * (∑ i : Fin n, w i * (MeasureTheory.volume {x : ℝ × (Fin v → ℝ) | |x.1| ≤ 1 ∧ (∀ p : Fin v, |x.2 p| ≤ 1) ∧ (∀ p r : Fin v, p ≠ r → K⁻¹ ≤ |x.2 p - x.2 r|) ∧ (fun x : ℝ × (Fin v → ℝ) => (x.1, fun j : Fin v => (U i 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin v, (U i p.succ - U i p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))) x ∈ T}).toReal)) (u (k + 1) - u k)) (fun (j : ℕ) (a : ℝ) => sSup (Set.image (fun x : ℝ => x - (j : ℝ) * r x) (Set.Icc 0 a)))) (fun a : ℝ => sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J))) := by
  classical
  intro D J hD hDJ d hd β hβ
  dsimp only
  intro γ hγ q hq hγq k v z u hadm κ hκ θ hθ
  obtain ⟨η, hη, Rₚ, hRₚ, hp⟩ := hprobability v hadm.2.1 κ hκ θ hθ
  obtain ⟨εg, hεg, Rg, hRg, hg⟩ :=
    hgeometry D J hD hDJ β hβ γ hγ q hq hγq k v z u hadm η hη
  refine ⟨min εg η, lt_min hεg hη, max Rg Rₚ, hRg.trans (le_max_left _ _), ?_⟩
  intro ε hε hε₀ N hN n₁ n₂ f₁ f₂ π₁ π₂ μ h F S hrec hpal
  obtain ⟨hn₁, hn₂, hf₁, hf₂, hd₁, hd₂, hπ₁, hπ₂, hsum₁, hsum₂, hμ,
    hm₁, hm₂, hS, hfull, hgap, hhmono, hhscale, hFfin, hrecord, hcard, hdesc⟩ := hrec
  have hk : k ≤ q := by omega
  have hfine : k + 6 * (J + 1) ≤ q := hadm.1
  have hz : z ≤ q := by have := hadm.2.2.2.2.1; omega
  have hNRg : Rg ≤ N := (le_max_left _ _).trans hN
  have hNRₚ : Rₚ ≤ N := (le_max_right _ _).trans hN
  have hN₁ : 1 ≤ N := by linarith [hRg.trans hNRg]
  have hεg' : ε ≤ εg := hε₀.trans (min_le_left _ _)
  have hεη : ε ≤ η := hε₀.trans (min_le_right _ _)
  let c : ℕ → ℝ → ℝ := fun b t =>
    ((Int.floor (t * (2 : ℝ) ^ h b) : ℝ) + 1 / 2) / (2 : ℝ) ^ h b
  let Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ := fun x =>
    (Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₁ x.1.1) (c z x.2)),
      Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₂ x.1.2) (c z x.2)))
  obtain ⟨K, δ, hK, hKη, hδ, hcover⟩ :=
    hg ε hε hεg' N hNRg n₁ n₂ f₁ f₂ h F S
      ⟨hf₁, hf₂, hd₁, hd₂, hgap, hhmono, hhscale, hFfin, hrecord, hdesc⟩
  have hsame : ∀ b : ℕ, b ≤ q →
      ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 →
      Int.floor (x.2 * (2 : ℝ) ^ h q) = Int.floor (y.2 * (2 : ℝ) ^ h q) →
      F b x = F b y := by
    intro b hb x hx y hy hxy hfloor
    apply (hrecord b hb x hx y hy).2
    intro a ha
    have heq := floor_eq_of_floor_eq_of_le (hhmono a q (ha.trans hb) le_rfl) hfloor
    refine ⟨heq, ?_⟩
    have hc : c a x.2 = c a y.2 := by dsimp [c]; rw [heq]
    have hi₁ : x.1.1 = y.1.1 := congrArg Prod.fst hxy
    have hi₂ : x.1.2 = y.1.2 := congrArg Prod.snd hxy
    intro j hj
    change Int.floor (N ^ _ * iteratedDeriv j (f₁ x.1.1) (c a x.2)) = _ ∧
      Int.floor (N ^ _ * iteratedDeriv j (f₂ x.1.2) (c a x.2)) = _
    simp only [hc, hi₁, hi₂]
    exact ⟨rfl, rfl⟩
  apply hp N hNRₚ (N ^ ε) K δ
    (N ^ (u (k + 1) - u k - (1 / (v : ℝ) + ((v : ℝ) + 1) / 2) / (q : ℝ)))
    (Real.one_le_rpow hN₁ hε.le)
    (Real.rpow_le_rpow_of_exponent_le hN₁ hεη) hK hKη hδ (by positivity)
    n₁ n₂ π₁ π₂ μ (h k) (F k) (F (k + 6 * (J + 1))) Z S
    hπ₁ hπ₂ hsum₁ hsum₂ hμ hm₁ hm₂ hS hfull
    (fun e he => (hgap e he).1)
  · intro x hx y hy heq
    apply (hrecord k hk x hx y hy).2
    intro a ha
    exact (hrecord _ hfine x hx y hy).1 heq a (by omega)
  · intro x hx y hy heq
    exact ((hrecord k hk x hx y hy).1 heq k le_rfl).1
  · refine ⟨h q, hhmono k q hk le_rfl, ?_⟩
    intro x hx y hy hxy hfloor
    refine ⟨hsame k hk x hx y hy hxy hfloor,
      hsame _ hfine x hx y hy hxy hfloor, ?_⟩
    have heq := floor_eq_of_floor_eq_of_le (hhmono z q hz le_rfl) hfloor
    have hc : c z x.2 = c z y.2 := by dsimp [c]; rw [heq]
    have hi₁ : x.1.1 = y.1.1 := congrArg Prod.fst hxy
    have hi₂ : x.1.2 = y.1.2 := congrArg Prod.snd hxy
    simp only [Z, hc, hi₁, hi₂]
  · apply hpal.trans
    apply ENNReal.ofReal_le_ofReal
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by have := hadm.2.2.1; omega))
  · exact hcover

end Submission.Obl.k4_matching_switching_target_certificate
