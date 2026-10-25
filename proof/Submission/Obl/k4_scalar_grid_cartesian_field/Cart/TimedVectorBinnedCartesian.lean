-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TimedVectorBinnedCartesian.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianVectorOriginalMass
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TimedFiberFits

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory MvPolynomial
open scoped ENNReal

/-- Actual per-state qualifying polynomials and fixed coefficient bins
supply the Cartesian fiber models. The output is an original-source
measurable field fit, with no incoming fiber-polynomial oracle. -/
theorem exists_original_cartesian_fields_from_timed_binned_witnesses {ι Ω X Y : Type*}
    [MeasurableSpace Ω] [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (cell : Ω → X × Y) (hcell : ∀ c, MeasurableSet {ω | cell ω = c})
    (D : ℕ) (v : X → ℝ) (w : Y → ℝ)
    (B Bt timeOrigin gap Bx By η ε E₀ E₁ H θ m M : ℝ)
    (hB : 1 ≤ B) (hBt : 1 ≤ Bt) (hgap : 0 < gap) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hη : 0 < η) (hε : 0 < ε) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hH : 0 ≤ H)
    (hθ : 0 < θ) (hm : 0 < m) (hM : 0 < M)
    (hv : ∀ x, |v x| ≤ B) (hw : ∀ y, |w y| ≤ B)
    (hlower : ENNReal.ofReal m ≤ μ A)
    (hcap : ∀ c, μ (A ∩ {ω | cell ω = c}) ≤ ENNReal.ofReal M)
    (hlight : θ*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ)) ≤ m/2)
    (hηmass : 2*M*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ))*η ≤ m)
    (hthinX : ∀ z, gridMean (finiteUniformWeights X)
      (fun x => if |v x-z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean (finiteUniformWeights Y)
      (fun y => if |w y-z| < gap then 1 else 0) ≤ By)
    (hloss : ((D : ℝ)+2)^2*Bx+((D : ℝ)+2)^2*By ≤ η^((D+2)^2)/2)
    (f : ι → ℝ → ℝ → ℝ) (G : ι → Ω → ℝ) (Pr Pc : ι → Ω → Polynomial ℝ)
    (htime : ∀ ω ∈ A, |timeOrigin+v (cell ω).1+w (cell ω).2| ≤ Bt)
    (hG : ∀ i, ∀ ω ∈ A, |G i ω| ≤ H)
    (hfield : ∀ i, ∀ ω ∈ A, |f i (v (cell ω).1) (w (cell ω).2)-G i ω| ≤ E₀)
    (hPr : ∀ i, ∀ ω ∈ A, (Pr i ω).natDegree ≤ D)
    (hPc : ∀ i, ∀ ω ∈ A, (Pc i ω).natDegree ≤ D)
    (hrowfit : ∀ i, ∀ ω ∈ A, |G i ω-(Pr i ω).eval (timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ E₁)
    (hcolfit : ∀ i, ∀ ω ∈ A, |G i ω-(Pc i ω).eval (timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ E₁)
    (hrowbins : ∀ ω ∈ A, ∀ ω' ∈ A, (cell ω).2=(cell ω').2 →
      ∀ i (k : Fin (D+1)), ⌊(Pr i ω).coeff k/ε⌋=⌊(Pr i ω').coeff k/ε⌋)
    (hcolbins : ∀ ω ∈ A, ∀ ω' ∈ A, (cell ω).1=(cell ω').1 →
      ∀ i (k : Fin (D+1)), ⌊(Pc i ω).coeff k/ε⌋=⌊(Pc i ω').coeff k/ε⌋) :
    let W := ((D : ℝ)+1)*(2*B/gap)^D
    let Err := E₀+E₁+2*((D : ℝ)+1)*ε*Bt^D
    ∃ (P : ι → MvPolynomial (Fin 2) ℝ) (S : Set Ω),
      (∀ i, (P i).totalDegree ≤ 2*D) ∧
      (∀ i, ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → |eval ![x,y] (P i)| ≤ (E₀+H)*W^2) ∧
      MeasurableSet S ∧ S ⊆ A ∧
      ENNReal.ofReal (θ*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ))*(η^((D+2)^2)/2)) ≤ μ S ∧
      ∀ ω ∈ S, ∀ i, |G i ω-eval ![v (cell ω).1,w (cell ω).2] (P i)| ≤ E₀+Err*(1+2*W+W^2) := by
  classical
  dsimp only
  let W := ((D : ℝ)+1)*(2*B/gap)^D
  let Err := E₀+E₁+2*((D : ℝ)+1)*ε*Bt^D
  have hErr : 0 ≤ Err := by dsimp [Err]; positivity
  have hfvals (i : ι) (x : X) (y : Y) (hx : ∃ ω ∈ A, cell ω=(x,y)) :
      |f i (v x) (w y)| ≤ E₀+H := by
    obtain ⟨ω,hω,hc⟩ := hx
    have hf := hfield i ω hω
    rw [hc] at hf
    have htri : |f i (v x) (w y)| ≤ |f i (v x) (w y)-G i ω|+|G i ω| := by
      simpa only [sub_add_cancel] using abs_add_le (f i (v x) (w y)-G i ω) (G i ω)
    exact htri.trans (add_le_add hf (hG i ω hω))
  have hfrows (i : ι) := exists_timed_fiber_polynomial_of_common_bins A cell v
    (fun y => timeOrigin+w y) (fun x y => f i (v x) (w y)) (G i) (Pr i)
    D ε Bt E₀ E₁ hε hBt (hPr i)
    (fun ω hω => by simpa only [add_assoc,add_comm,add_left_comm] using htime ω hω)
    (hfield i)
    (fun ω hω => by simpa only [add_assoc,add_comm,add_left_comm] using hrowfit i ω hω)
    (fun ω hω ω' hω' hs => hrowbins ω hω ω' hω' hs i)
  have hfcols' (i : ι) := exists_timed_fiber_polynomial_of_common_bins A
    (fun ω => ((cell ω).2,(cell ω).1)) w (fun x => timeOrigin+v x)
    (fun y x => f i (v x) (w y)) (G i) (Pc i) D ε Bt E₀ E₁ hε hBt
    (hPc i) htime (hfield i) (hcolfit i)
    (fun ω hω ω' hω' hs => hcolbins ω hω ω' hω' hs i)
  have hfcols (i : ι) (x : X) : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ y, (∃ ω ∈ A, cell ω=(x,y)) → |f i (v x) (w y)-p.eval (w y)| ≤ Err := by
    obtain ⟨p,hp,hfit⟩ := hfcols' i x
    refine ⟨p,hp,?_⟩
    intro y hy
    apply hfit y
    obtain ⟨ω,hω,hc⟩ := hy
    exact ⟨ω,hω,by rw [hc]⟩
  obtain ⟨P,hP,hNorm,hMeas,hMass⟩ := exists_cartesian_polynomial_fields_original_mass
    μ A hA cell hcell D v w B gap Bx By η Err (E₀+H) θ m M
    (le_trans (by norm_num) hB) hgap hBx hBy hη hErr (by positivity)
    hθ hm hM hv hw hlower hcap hlight hηmass hthinX hthinY hloss f hfvals hfrows hfcols
  let S := {ω | ω ∈ A ∧ ∀ i, |f i (v (cell ω).1) (w (cell ω).2)-
    eval ![v (cell ω).1,w (cell ω).2] (P i)| ≤ Err*(1+2*W+W^2)}
  refine ⟨P,S,hP,hNorm,hMeas,(fun ω hω => hω.1),hMass,?_⟩
  intro ω hω i
  have hf : |G i ω-f i (v (cell ω).1) (w (cell ω).2)| ≤ E₀ := by
    simpa only [abs_sub_comm] using hfield i ω hω.1
  exact (abs_sub_le (G i ω) (f i (v (cell ω).1) (w (cell ω).2))
    (eval ![v (cell ω).1,w (cell ω).2] (P i))).trans (add_le_add hf (hω.2 i))

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
