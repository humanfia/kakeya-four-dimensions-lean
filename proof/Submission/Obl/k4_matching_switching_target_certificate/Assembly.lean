-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/Assembly.lean.
import ChallengeDeps
import Submission.Obl.k4_matching_switching_target_certificate.Certificate

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

/-- The remaining uniform target construction, with its fixed volume coefficient
chosen before the loss and scale. -/
def TargetConstruction : Prop :=
  ∀ (J q k m z : ℕ) (β u : ℕ → ℝ) (γ : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ε N : ℝ) (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
      (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
      (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (H : Det J β γ q k m z N ε f₁ f₂ h F S),
      ε ≤ 1 / (q : ℝ) → 32 ≤ N ^ (1 / (q : ℝ)) →
      (∀ a : ℕ, a ≤ q → Measurable (F a) ∧ (F a '' S).Finite) →
      (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S,
        ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε)) →
      ∃ δ : ℝ, 0 < δ ∧ H.TargetCovers u C δ

/-- All the frozen quantifiers and geometric cover clauses follow from the
uniform moving-target construction. -/
theorem geometricCover_of_targetConstruction (htarget : TargetConstruction) : ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ β : ℕ → ℝ, ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)) → (fun r : ℝ → ℝ => (fun l : ℕ → ℝ → ℝ => ∀ γ : ℝ, 0 < γ → ∀ q : ℕ, 1 ≤ q → 4 ≤ γ * (q : ℝ) → ∀ (k m z : ℕ) (u : ℕ → ℝ), (k + 6 * (J + 1) ≤ q ∧ 1 ≤ m ∧ m ≤ J ∧ β m < 2 ∧ z ≤ k ∧ γ ≤ (z : ℝ) / (q : ℝ) ∧ ∀ x ∈ Set.Icc ((z : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)), r x = (x - β m) / (m : ℝ) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ m → (x - β j) / (j : ℝ) < r x) ∧ (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧ (∀ i : ℕ, 1 ≤ i → m + i ≤ J → γ ≤ l (m + i) x + (i : ℝ) * r x - β m)) → ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R : ℝ, 2 ≤ R ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N : ℝ, R ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)), ((fun c : ℕ → ℝ → ℝ => (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧ (∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ J → |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧ (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b) ∧ (∀ a : ℕ, a ≤ q → N ^ (r ((a : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h a ∧ (2 : ℝ) ^ h a ≤ 2 * N ^ (r ((a : ℝ) / (q : ℝ)))) ∧ (∀ a : ℕ, a ≤ q → Measurable (F a) ∧ (F a '' S).Finite) ∧ (∀ a : ℕ, a ≤ q → ∀ x ∈ S, ∀ y ∈ S, F a x = F a y ↔ ∀ b : ℕ, b ≤ a → Int.floor (x.2 * (2 : ℝ) ^ h b) = Int.floor (y.2 * (2 : ℝ) ^ h b) ∧ ∀ j : ℕ, j ≤ J → Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c b x.2)) = Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c b y.2)) ∧ Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c b x.2)) = Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c b y.2))) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S, ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε))) (fun b t => ((Int.floor (t * (2 : ℝ) ^ h b) : ℝ) + 1 / 2) / (2 : ℝ) ^ h b)) → (fun H : ℕ => (fun F₀ : ((Fin n₁ × Fin n₂) × ℝ) → ℕ => (fun F₁ : ((Fin n₁ × Fin n₂) × ℝ) → ℕ => (fun Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ => (fun σ : ((Fin n₁ × Fin n₂) × ℝ) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => (fun Φ : (Fin (m + 1) → ℝ) → ℝ → (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => (fun V : ℝ => ∃ K δ : ℝ, 2 ≤ K ∧ K ≤ N ^ η ∧ 0 < δ ∧ (∀ a ∈ S, ∃ (A : Finset ℕ) (C : ℕ → (ℤ × ℤ) → Bool → ℝ) (T : Set (ℝ × (Fin m → ℝ))), |σ a a| ≤ 1 ∧ (A.card : ℝ) ≤ K ∧ (∀ e ∈ S, F₀ e ∈ A → ∀ c : Bool, |C (F₀ e) (Z e) c| ≤ K) ∧ (∀ e ∈ S, F₀ e ∈ A → 2 / K ≤ |C (F₀ e) (Z e) true - C (F₀ e) (Z e) false|) ∧ MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (K * V) ∧ ∀ (E W : ℕ → ((Fin n₁ × Fin n₂) × ℝ)) (c : ℕ → Bool), E 0 = a → (∀ p : ℕ, p ≤ m + 1 → E p ∈ S) → (∀ p : ℕ, p ≤ m → W p ∈ S ∧ F₁ (W p) = F₁ (E p) ∧ (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧ Int.floor ((W p).2 * (2 : ℝ) ^ H) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ H)) → (∀ p : ℕ, p ≤ m + 1 → F₀ (E p) ∈ A) ∧ (∀ p : ℕ, p ≤ m → F₀ (W p) ∈ A) ∧ ∀ x : ℝ × (Fin m → ℝ), |x.1 - σ a (E (m + 1))| ≤ δ → (∀ p : Fin m, |x.2 p - σ a (E ((p : ℕ) + 1))| ≤ δ) → Φ (fun p : Fin (m + 1) => C (F₀ (W p)) (Z (W p)) (c p)) (σ a a) x ∈ T)) (N ^ (u (k + 1) - u k - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ)))) ((fun (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (x : ℝ × (Fin m → ℝ)) => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))))) ((fun (a e : ((Fin n₁ × Fin n₂) × ℝ)) => (e.2 - (((Int.floor (a.2 * (2 : ℝ) ^ H) : ℝ) + 1 / 2) / (2 : ℝ) ^ H)) * (2 : ℝ) ^ H))) (fun x => (Int.floor (N ^ (β m + 6 / (q : ℝ)) * iteratedDeriv m (f₁ x.1.1) (((Int.floor (x.2 * (2 : ℝ) ^ h z) : ℝ) + 1 / 2) / (2 : ℝ) ^ h z)), Int.floor (N ^ (β m + 6 / (q : ℝ)) * iteratedDeriv m (f₂ x.1.2) (((Int.floor (x.2 * (2 : ℝ) ^ h z) : ℝ) + 1 / 2) / (2 : ℝ) ^ h z))))) (F (k + 6 * (J + 1)))) (F k)) (h k)) (fun j a => sSup (Set.image (fun x : ℝ => x - (j : ℝ) * r x) (Set.Icc 0 a)))) (fun a => sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J))) := by
  intro D J hD hDJ β hβ
  dsimp only
  intro γ hγ q hq hγq k m z u hadm η hη
  rcases hadm with ⟨hkq, hm, hmJ, hβm, hzk, hγz, hadm⟩
  obtain ⟨C, hC, htargets⟩ := htarget J q k m z β u γ
  obtain ⟨ε₀, hε₀, R, hR, hparams⟩ := cover_parameters J k m q hq C η hη
  refine ⟨ε₀, hε₀, R, hR, ?_⟩
  intro ε hε hεle N hN n₁ n₂ f₁ f₂ h F S hdata
  rcases hdata with ⟨hf₁, hf₂, hB₁, hB₂, hS, hmono, hdepth, hfinite, hrec, hhom⟩
  have hN1 : 1 ≤ N := by linarith
  have hJ : 1 ≤ J := by omega
  have hzero : ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ β j = 0 := by
    obtain ⟨j, hj, hjD, hj0⟩ := hβ.2
    exact ⟨j, hj, hjD.trans hDJ.le, hj0⟩
  let H : Det J β γ q k m z N ε f₁ f₂ h F S :=
    { hJ := hJ
      hβ := hβ.1
      hzero := hzero
      hγ := hγ
      hq := hq
      hγq := hγq
      hkq := hkq
      hm := hm
      hmJ := hmJ
      hβm := hβm
      hzk := hzk
      hγz := hγz
      hadm := hadm
      hN := hN1
      hε := hε
      hf₁ := hf₁
      hf₂ := hf₂
      hB₁ := hB₁
      hB₂ := hB₂
      hS := hS
      hmono := hmono
      hdepth := hdepth
      hrec := hrec }
  obtain ⟨hεq, hroot, hscale⟩ := hparams ε hε hεle N hN
  obtain ⟨δ, hδ, ht⟩ := htargets ε N n₁ n₂ f₁ f₂ h F S H hεq hroot hfinite hhom
  have hcover := H.covers_of_targets u hC hεq hroot hscale hδ ht
  simpa only [GeometricCovers, ntime_eq, dcenter, referencePalette,
    k4_matching_homogeneous_records.dyadicCenter, endpointMap] using hcover

end Submission.Obl.k4_matching_switching_target_certificate
