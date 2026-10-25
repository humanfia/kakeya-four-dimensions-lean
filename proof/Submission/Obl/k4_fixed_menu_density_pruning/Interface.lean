import Submission.Obl.k4_quadratic_finite_greedy_cover.Interface

set_option linter.unusedVariables false

namespace Submission.Obl.k4_fixed_menu_density_pruning

noncomputable section

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Line × ℝ
abbrev Observation := EuclideanSpace ℝ (Fin 3) × ℤ

-- Reuse the accepted frozen coordinate and path interfaces from o170.
abbrev x := Submission.Obl.k4_quadratic_finite_greedy_cover.x
abbrev y := Submission.Obl.k4_quadratic_finite_greedy_cover.y
abbrev v := Submission.Obl.k4_quadratic_finite_greedy_cover.v
abbrev δ := Submission.Obl.k4_quadratic_finite_greedy_cover.δ
abbrev obs := Submission.Obl.k4_quadratic_finite_greedy_cover.obs
abbrev fmt := Submission.Obl.k4_quadratic_finite_greedy_cover.fmt
abbrev chart := Submission.Obl.k4_quadratic_finite_greedy_cover.chart
abbrev prob := Submission.Obl.k4_quadratic_finite_greedy_cover.prob
abbrev path := Submission.Obl.k4_quadratic_finite_greedy_cover.path

-- These predicates are the applied lambdas in o209, without any added hypotheses.
def greedyCover :=
  (fun (Nk L:ℝ) (W:ℕ) (ω:Fin W→ ℝ) (ν:Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ))) (B:Fin W→ ℝ) (d₁ ρ gain:ℝ) (m:ℕ) (r:ℕ→ ℝ) (T:ℕ→ ℕ) (C:ℕ) (lev:Fin C→ ℕ) (γ:Fin C→ Fin W) (j:Fin C→ ℕ) (A:Fin C→ Set (ℕ×(Fin 6→ ℝ))) (F:Fin C→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (Mg Dg:ℕ) (ε:ℝ)=>∃ (i:ℕ) (h:ℝ) (n:ℕ) (old:Fin n→ Fin C) (R':Fin n→ MvPolynomial (Fin 4) ℝ) (A':Fin n→ Set (ℕ×(Fin 6→ ℝ))) (V:Fin n→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)),i < m∧ gain ≤ h∧ h ≤ 1/8∧ (∃ z:ℕ,h=gain+(z:ℝ)*(ρ*gain))∧ r i+2*h*L ≤ L∧ (n:ℝ) ≤ Nk^Mg∧ (∀ a,lev (old a)=i∧ 0 < ν (γ (old a)) (A (old a))∧ (R' a).totalDegree ≤ 2∧ (∀ e,|(R' a).coeff e| ≤ Nk^Mg)∧ MeasurableSet (A' a)∧ A' a ⊆ A (old a)∧ (∀ q,fmt 6 (Nk^Mg) Dg {z | (q,z) ∈ A' a})∧ (∀ l ∈ A' a,∀ t ∈ Set.Icc ((j (old a):ℝ)/(2:ℝ)^T i) (((j (old a):ℝ)+1)/(2:ℝ)^T i),|MvPolynomial.eval (x l t) (R' a)| ≤ Nk^(4*ρ*gain*L+4*ε)*δ Nk (r i+h*L)∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (R' a))| ≤ Nk^(4*ρ*gain*L+4*ε)*B (γ (old a))∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (R' a)))| ≤ Nk^(4*ρ*gain*L+4*ε)*B (γ (old a))^2/δ Nk (r i+h*L))∧ MeasurableSet (V a)∧ V a ⊆ {p | (∃ b:Fin C,lev b=m - 1∧ γ b=γ (old a)∧ p ∈ F b)∧ p.1 ∈ A' a∧ p.2 ∈ Set.Icc ((j (old a):ℝ)/(2:ℝ)^T i) (((j (old a):ℝ)+1)/(2:ℝ)^T i)∧ B (γ (old a))/Nk^(4*ρ*gain*L+4*ε) ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (R' a))|}∧ ENNReal.ofReal (Nk^(-((d₁*h+4*ρ*gain)*L) - 4*ε)/(2:ℝ)^T i)*ν (γ (old a)) (A (old a)) ≤ ((ν (γ (old a))).prod MeasureTheory.volume) (V a))∧ (∀ a a',a ≠ a'→ old a=old a'→ Disjoint (A' a) (A' a'))∧ (∀ b:Fin C,((Finset.univ.filter (fun a=>old a=b)).card:ℝ) ≤ Nk^((d₁*h+4*ρ*gain)*L+4*ε))∧ (∀ a a',a ≠ a'→ γ (old a)=γ (old a')→ Disjoint (V a) (V a'))∧ ENNReal.ofReal (Nk^(-ε)) ≤ ∑ a,ENNReal.ofReal (ω (γ (old a)))*((ν (γ (old a))).prod MeasureTheory.volume) (V a))

def menuDepth :=
  (fun (L s h δ₀:ℝ) => min L (max 0 (s * L + h * L - 2 * δ₀ * L)))

def CleanCover :=
  (fun (Nk L:ℝ) (W:ℕ) (ω:Fin W→ ℝ) (ν:Fin W→ MeasureTheory.Measure (ℕ × (Fin 6→ ℝ))) (B:Fin W→ ℝ) (f:ℝ→ ℝ) (d₁ ρ gain δ₀:ℝ) (m:ℕ) (s r:ℕ→ ℝ) (T:ℕ→ ℕ) (κ:ℝ) (C:ℕ) (lev:Fin C→ ℕ) (γ:Fin C→ Fin W) (j:Fin C→ ℕ) (Q:Fin C→ Matrix (Fin 2) (Fin 2) ℝ) (A:Fin C→ Set (ℕ × (Fin 6→ ℝ))) (F:Fin C→ Set ((ℕ × (Fin 6→ ℝ)) × ℝ)) (Mg Dg:ℕ) (τ ε:ℝ) => ∃ (i:ℕ) (h:ℝ) (n:ℕ) (old:Fin n→ Fin C) (R':Fin n→ MvPolynomial (Fin 4) ℝ) (A':Fin n→ Set (ℕ × (Fin 6→ ℝ))) (V:Fin n→ Set ((ℕ × (Fin 6→ ℝ)) × ℝ)) (U:Fin C→ Set ((ℕ × (Fin 6→ ℝ)) × ℝ)),i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ (∃ z:ℕ,h = gain + (z:ℝ) * (ρ * gain)) ∧ r i + 2 * h * L ≤ L ∧ (n:ℝ) ≤ Nk ^ Mg ∧ (∀ a,lev (old a) = i ∧ 0 < ν (γ (old a)) (A (old a)) ∧ (R' a).totalDegree ≤ 2 ∧ (∀ e,|(R' a).coeff e| ≤ Nk ^ Mg) ∧ MeasurableSet (A' a) ∧ A' a ⊆ A (old a) ∧ (∀ q,fmt 6 (Nk ^ Mg) Dg {z | (q,z) ∈ A' a}) ∧ (∀ l ∈ A' a,∀ t ∈ Set.Icc ((j (old a):ℝ) / (2:ℝ) ^ T i) (((j (old a):ℝ) + 1) / (2:ℝ) ^ T i),|MvPolynomial.eval (x l t) (R' a)| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (R' a))| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (R' a)))| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ^ 2 / δ Nk (r i + h * L)) ∧ MeasurableSet (V a) ∧ V a ⊆ {p | p ∈ U (old a) ∧ p.1 ∈ A' a ∧ p.2 ∈ Set.Icc ((j (old a):ℝ) / (2:ℝ) ^ T i) (((j (old a):ℝ) + 1) / (2:ℝ) ^ T i) ∧ B (γ (old a)) / Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (R' a))|} ∧ ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) / (2 * (2:ℝ) ^ T i)) * ν (γ (old a)) (A (old a)) ≤ ((ν (γ (old a))).prod MeasureTheory.volume) (V a) ∧ ENNReal.ofReal (Nk ^ (-f (r i)) * |Matrix.det (Q (old a))| / (2 * (2:ℝ) ^ T i * κ)) ≤ ((ν (γ (old a))).prod MeasureTheory.volume) (U (old a)) ∧ (((ν (γ (old a))).prod MeasureTheory.volume).restrict (V a)).map (obs (B (γ (old a))) (δ Nk (menuDepth L (s i) h δ₀))) ≤ ENNReal.ofReal (Nk ^ (-f (menuDepth L (s i) h δ₀) + τ)) • (MeasureTheory.volume.prod MeasureTheory.Measure.count) ∧ (((ν (γ (old a))).prod MeasureTheory.volume).restrict (V a)).map (obs (B (γ (old a))) (δ Nk L)) ≤ ENNReal.ofReal (Nk ^ (-f L + τ)) • (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧ (∀ b,MeasurableSet (U b) ∧ U b ⊆ F b ∧ (((ν (γ b)).prod MeasureTheory.volume).restrict (U b)).map (obs (B (γ b)) (δ Nk (menuDepth L (s i) 0 δ₀))) ≤ ENNReal.ofReal (Nk ^ (-f (menuDepth L (s i) 0 δ₀) + τ)) • (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧ (∀ a a',a ≠ a'→ old a = old a'→ Disjoint (A' a) (A' a')) ∧ (∀ b:Fin C,((Finset.univ.filter (fun a => old a = b)).card:ℝ) ≤ Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) ∧ (∀ a a',a ≠ a'→ γ (old a) = γ (old a')→ Disjoint (V a) (V a')) ∧ ENNReal.ofReal (Nk ^ (-ε) / 2) ≤ ∑ a,ENNReal.ofReal (ω (γ (old a))) * ((ν (γ (old a))).prod MeasureTheory.volume) (V a))

def Statement : Prop :=
  ∀ d₁ κ₁ S η ρ:ℝ,0 ≤ d₁→ d₁ < 1→ 0 < κ₁→ κ₁ ≤ 1→ 0 < S→ 0 < η→ 0 < ρ→ ρ ≤ 1 / 4→ d₁ + ρ < 1→ ∀ (m:ℕ) (s:ℕ→ ℝ) (gain δ₀:ℝ),(0 < m ∧ 0 < s 0 ∧ (∀ i,i + 1 < m→ s i < s (i + 1)) ∧ s (m - 1) = 1)→ 0 < gain→ gain ≤ 1 / 8→ 0 < δ₀→ δ₀ ≤ ρ * gain→ ∀ N K L d W ω ν E P B f g G,prob N K L d S η W ω ν E P B f g G→ ∀ Mp Dp Mg Dg:ℕ,∀ τ:ℝ,0 < τ→ ∃ ε₀ σ₀:ℝ,0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < σ₀ ∧ σ₀ ≤ 1 ∧ ∃ k₀:ℕ,∀ k,k₀ ≤ k→ ∀ ε σ:ℝ,0 < ε→ ε ≤ ε₀→ 0 < σ→ σ ≤ σ₀→ ∀ r T nw κ C lev par γ j c u Q R A F lst,path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst→ greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε→ CleanCover (N k) L (W k) (ω k) (ν k) (B k) f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε

end

end Submission.Obl.k4_fixed_menu_density_pruning
