-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TimedMeshCartesian.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TimedVectorListedCartesian
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.PolynomialWitnessTransfer
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianMeshTransfer

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory MvPolynomial
open scoped ENNReal

/-- Actual witness-time fits and a fine Cartesian mesh produce common
component fields at the actual source points. Both mesh errors are
explicit, and the success floor is in the unchanged original law. -/
theorem exists_timed_mesh_cartesian_field_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι Ω X Y : Type*}
      [MeasurableSpace Ω] [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
      (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω), MeasurableSet A →
      ∀ (cell : Ω → X × Y), (∀ c, MeasurableSet {ω | cell ω=c}) →
      ∀ (v : X → ℝ) (w : Y → ℝ), Function.Injective v → Function.Injective w →
      ∀ (B Bt timeOrigin gap Bx By η ε ρ H Hp K θ m M δt δx : ℝ),
      1 ≤ B → 1 ≤ Bt → 0 < gap → 0 ≤ Bx → 0 ≤ By →
      0 < η → 0 < ε → 0 ≤ ρ → 0 ≤ H → 0 ≤ Hp → 1 ≤ K →
      0 < θ → 0 < m → 0 < M → 0 ≤ δt →
      (∀ x, |v x| ≤ B) → (∀ y, |w y| ≤ B) →
      ENNReal.ofReal m ≤ μ A →
      (∀ c, μ (A ∩ {ω | cell ω=c}) ≤ ENNReal.ofReal M) →
      θ*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ)) ≤ (m/K^3)/2 →
      2*M*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ))*η ≤ m/K^3 →
      (∀ z, gridMean (finiteUniformWeights X)
        (fun x => if |v x-z| < gap then 1 else 0) ≤ Bx) →
      (∀ z, gridMean (finiteUniformWeights Y)
        (fun y => if |w y-z| < gap then 1 else 0) ≤ By) →
      ((D : ℝ)+2)^2*Bx+((D : ℝ)+2)^2*By ≤ η^((D+2)^2)/2 →
      ∀ (G : ι → Ω → ℝ) (Pr Pc : ι → Ω → Polynomial ℝ)
        (sourceTime : Ω → ℝ) (actual : Ω → Fin 2 → ℝ),
      (∀ ω ∈ A, |timeOrigin+v (cell ω).1+w (cell ω).2| ≤ Bt) →
      (∀ ω ∈ A, |sourceTime ω| ≤ Bt) →
      (∀ ω ∈ A, |sourceTime ω-(timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ δt) →
      (∀ ω ∈ A, actual ω ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B)) →
      (∀ ω ∈ A, |actual ω 0-v (cell ω).1|+|actual ω 1-w (cell ω).2| ≤ δx) →
      (∀ i, ∀ ω ∈ A, |G i ω| ≤ H) →
      (∀ i, ∀ ω ∈ A, (Pr i ω).natDegree ≤ D) →
      (∀ i, ∀ ω ∈ A, (Pc i ω).natDegree ≤ D) →
      (∀ i, ∀ ω ∈ A, ∀ k ≤ D, |(Pr i ω).coeff k| ≤ Hp) →
      (∀ i, ∀ ω ∈ A, ∀ k ≤ D, |(Pc i ω).coeff k| ≤ Hp) →
      (∀ i, ∀ ω ∈ A, |G i ω-(Pr i ω).eval (sourceTime ω)| ≤ ρ) →
      (∀ i, ∀ ω ∈ A, |G i ω-(Pc i ω).eval (sourceTime ω)| ≤ ρ) →
      (∀ j : ι → ℤ, MeasurableSet {ω | (fun i => ⌊G i ω/ε⌋)=j}) →
      (∀ c, MeasurableSet {ω | (fun i (k : Fin (D+1)) => ⌊(Pr i ω).coeff k/ε⌋)=c}) →
      (∀ c, MeasurableSet {ω | (fun i (k : Fin (D+1)) => ⌊(Pc i ω).coeff k/ε⌋)=c}) →
      ∀ (L₀ : X × Y → Finset (ι → ℤ))
        (Lr : Y → Finset (ι → Fin (D+1) → ℤ)) (Lc : X → Finset (ι → Fin (D+1) → ℤ)),
      (∀ c, ((L₀ c).card : ℝ) ≤ K) →
      (∀ y, ((Lr y).card : ℝ) ≤ K) → (∀ x, ((Lc x).card : ℝ) ≤ K) →
      (∀ ω ∈ A, (fun i => ⌊G i ω/ε⌋) ∈ L₀ (cell ω)) →
      (∀ ω ∈ A, (fun i (k : Fin (D+1)) => ⌊(Pr i ω).coeff k/ε⌋) ∈ Lr (cell ω).2) →
      (∀ ω ∈ A, (fun i (k : Fin (D+1)) => ⌊(Pc i ω).coeff k/ε⌋) ∈ Lc (cell ω).1) →
      let W := ((D : ℝ)+1)*(2*B/gap)^D
      let Rho := ρ+((D : ℝ)+1)*(D : ℝ)*Hp*Bt^D*δt
      let Err := ε+Rho+2*((D : ℝ)+1)*ε*Bt^D
      ∃ (P : ι → MvPolynomial (Fin 2) ℝ) (S : Set Ω),
        (∀ i, (P i).totalDegree ≤ 2*D) ∧
        (∀ i, ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → |eval ![x,y] (P i)| ≤ (ε+H)*W^2) ∧
        MeasurableSet S ∧ S ⊆ A ∧
        ENNReal.ofReal (θ*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ))*(η^((D+2)^2)/2)) ≤ μ S ∧
        ∀ ω ∈ S, ∀ i, |G i ω-eval (actual ω) (P i)| ≤
          ε+Err*(1+2*W+W^2)+C*((ε+H)*W^2)*δx := by
  obtain ⟨C,hC,hmove⟩ := exists_cartesian_mesh_fit_transfer_constant (2*D)
  refine ⟨C,hC,?_⟩
  intro ι Ω X Y _ _ _ _ _ μ _ A hA cell hcell v w hinjv hinjw
    B Bt timeOrigin gap Bx By η ε ρ H Hp K θ m M δt δx
    hB hBt hgap hBx hBy hη hε hρ hH hHp hK hθ hm hM hδt hv hw
    hlower hcap hlight hηmass hthinX hthinY hloss G Pr Pc sourceTime actual
    htime hsourceTime htimeDist hactual hspaceDist hG hPr hPc hPrcoeff hPccoeff
    hrowfit hcolfit hmG hmPr hmPc L₀ Lr Lc hc₀ hcr hcc hk₀ hkr hkc
  dsimp only
  let Rho := ρ+((D : ℝ)+1)*(D : ℝ)*Hp*Bt^D*δt
  have hRho : 0 ≤ Rho := by
    dsimp only [Rho]
    have hBt0 : 0 ≤ Bt := le_trans (by norm_num) hBt
    positivity
  have hrow (i : ι) (ω : Ω) (hω : ω ∈ A) :
      |G i ω-(Pr i ω).eval (timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ Rho :=
    polynomial_fit_at_nearby_time D (Pr i ω) (hPr i ω hω) Hp Bt hHp hBt
      (hPrcoeff i ω hω) (G i ω) (sourceTime ω)
      (timeOrigin+v (cell ω).1+w (cell ω).2) ρ δt
      (hsourceTime ω hω) (htime ω hω) (hrowfit i ω hω) (htimeDist ω hω)
  have hcol (i : ι) (ω : Ω) (hω : ω ∈ A) :
      |G i ω-(Pc i ω).eval (timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ Rho :=
    polynomial_fit_at_nearby_time D (Pc i ω) (hPc i ω hω) Hp Bt hHp hBt
      (hPccoeff i ω hω) (G i ω) (sourceTime ω)
      (timeOrigin+v (cell ω).1+w (cell ω).2) ρ δt
      (hsourceTime ω hω) (htime ω hω) (hcolfit i ω hω) (htimeDist ω hω)
  obtain ⟨P,S,hP,hNorm,hSm,hSA,hMass,hfit⟩ :=
    exists_original_cartesian_fields_from_timed_local_lists μ A hA cell hcell D v w hinjv hinjw
      B Bt timeOrigin gap Bx By η ε Rho H K θ m M hB hBt hgap hBx hBy hη hε hRho hH hK
      hθ hm hM hv hw hlower hcap hlight hηmass hthinX hthinY hloss G Pr Pc
      htime hG hPr hPc hrow hcol hmG hmPr hmPc L₀ Lr Lc hc₀ hcr hcc hk₀ hkr hkc
  refine ⟨P,S,hP,hNorm,hSm,hSA,hMass,?_⟩
  let W := ((D : ℝ)+1)*(2*B/gap)^D
  apply hmove S P G (fun ω => ![v (cell ω).1,w (cell ω).2]) actual B ((ε+H)*W^2)
    (ε+(ε+Rho+2*((D : ℝ)+1)*ε*Bt^D)*(1+2*W+W^2)) δx hB (by positivity) hP
  · intro i z hz
    have hz0 : |z 0| ≤ B := abs_le.mpr ⟨hz.1 0,hz.2 0⟩
    have hz1 : |z 1| ≤ B := abs_le.mpr ⟨hz.1 1,hz.2 1⟩
    have heq : ![z 0,z 1]=z := by ext j; fin_cases j <;> rfl
    simpa only [heq] using hNorm i (z 0) (z 1) hz0 hz1
  · intro ω _
    constructor <;> intro j <;> fin_cases j
    · exact (abs_le.mp (hv _)).1
    · exact (abs_le.mp (hw _)).1
    · exact (abs_le.mp (hv _)).2
    · exact (abs_le.mp (hw _)).2
  · intro ω hω
    exact hactual ω (hSA hω)
  · intro ω hω
    exact hspaceDist ω (hSA hω)
  · exact hfit

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
