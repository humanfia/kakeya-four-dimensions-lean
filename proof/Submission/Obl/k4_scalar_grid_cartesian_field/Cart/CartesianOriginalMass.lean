-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/CartesianOriginalMass.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianCells
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianInterpolation

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory MvPolynomial
open scoped ENNReal

theorem measurableSet_finite_observation_predicate {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I] (obs : Ω → I)
    (hobs : ∀ i, MeasurableSet {ω | obs ω = i}) (P : I → Prop) :
    MeasurableSet {ω | P (obs ω)} := by
  classical
  have heq : {ω | P (obs ω)} = ⋃ i : I, {ω | P i ∧ obs ω = i} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨obs ω, h, rfl⟩
    · rintro ⟨i, hi, hω⟩
      simpa only [hω] using hi
  rw [heq]
  exact MeasurableSet.iUnion fun i => (MeasurableSet.const (P i)).inter (hobs i)

/-- The Cartesian polynomial construction on the ORIGINAL incidence
law. Heavy cells are constructed internally and their original floors
turn successful target counts back into original unnormalized mass. -/
theorem exists_cartesian_polynomial_field_original_mass {Ω X Y : Type*}
    [MeasurableSpace Ω] [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (cell : Ω → X × Y) (hcell : ∀ c, MeasurableSet {ω | cell ω = c})
    (D : ℕ) (v : X → ℝ) (w : Y → ℝ)
    (B gap Bx By η E H θ m M : ℝ)
    (hB : 0 ≤ B) (hgap : 0 < gap) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hη : 0 < η) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hθ : 0 < θ) (hm : 0 < m) (hM : 0 < M)
    (hv : ∀ x, |v x| ≤ B) (hw : ∀ y, |w y| ≤ B)
    (hlower : ENNReal.ofReal m ≤ μ A)
    (hcap : ∀ c, μ (A ∩ {ω | cell ω = c}) ≤ ENNReal.ofReal M)
    (hlight : θ * ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) ≤ m/2)
    (hηmass : 2 * M * ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) * η ≤ m)
    (hthinX : ∀ z, gridMean (finiteUniformWeights X)
      (fun x => if |v x - z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean (finiteUniformWeights Y)
      (fun y => if |w y - z| < gap then 1 else 0) ≤ By)
    (hloss : ((D : ℝ)+2)^2 * Bx + ((D : ℝ)+2)^2 * By ≤ η^((D+2)^2)/2)
    (f : ℝ → ℝ → ℝ)
    (hvals : ∀ x y, (∃ ω ∈ A, cell ω = (x,y)) → |f (v x) (w y)| ≤ H)
    (hrows : ∀ y, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ x, (∃ ω ∈ A, cell ω = (x,y)) → |f (v x) (w y) - p.eval (v x)| ≤ E)
    (hcols : ∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ y, (∃ ω ∈ A, cell ω = (x,y)) → |f (v x) (w y) - p.eval (w y)| ≤ E) :
    let W := ((D : ℝ)+1) * (2*B/gap)^D
    ∃ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ 2*D ∧
      (∀ x y : ℝ, |x| ≤ B → |y| ≤ B → |eval ![x,y] P| ≤ H*W^2) ∧
      MeasurableSet {ω | ω ∈ A ∧ |f (v (cell ω).1) (w (cell ω).2) -
          eval ![v (cell ω).1,w (cell ω).2] P| ≤ E*(1+2*W+W^2)} ∧
      ENNReal.ofReal (θ * ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) *
          (η^((D+2)^2)/2)) ≤
        μ {ω | ω ∈ A ∧ |f (v (cell ω).1) (w (cell ω).2) -
          eval ![v (cell ω).1,w (cell ω).2] P| ≤ E*(1+2*W+W^2)} := by
  classical
  dsimp only
  let N := (Fintype.card X : ℝ) * (Fintype.card Y : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hlight' : θ * (Fintype.card (X × Y) : ℝ) ≤ m/2 := by
    simpa only [Fintype.card_prod, Nat.cast_mul] using hlight
  obtain ⟨F,hfloor,hwitness,_,hcard⟩ := exists_original_heavy_grid_density μ A cell θ m M
    hθ hm hM hlower hcap hlight'
  let R : X → Y → Prop := fun x y => (x,y) ∈ F
  have hdensity : η ≤ gridMean (finiteUniformWeights X) (fun x =>
      gridMean (finiteUniformWeights Y) (fun y => gridFlag (R x y))) := by
    rw [uniform_grid_relation_density R]
    suffices h : η ≤ (F.card : ℝ) / N by simpa [R, N] using h
    apply (le_div_iff₀ hN).mpr
    have hmcard : m ≤ (F.card : ℝ) * (2*M) := (div_le_iff₀ (by positivity)).mp hcard
    have hnum : (η*N)*(2*M) ≤ (F.card : ℝ)*(2*M) := by
      calc
        (η*N)*(2*M) = 2*M*N*η := by ring
        _ ≤ m := hηmass
        _ ≤ _ := hmcard
    have htwoM : (0 : ℝ) < 2*M := by positivity
    exact (mul_le_mul_iff_left₀ htwoM).mp hnum
  have hfvals : ∀ x y, R x y → |f (v x) (w y)| ≤ H := by
    intro x y hxy
    exact hvals x y (hwitness (x,y) hxy)
  have hfrows (y : Y) : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ x, R x y → |f (v x) (w y) - p.eval (v x)| ≤ E := by
    obtain ⟨p,hp,hfit⟩ := hrows y
    exact ⟨p,hp,fun x hxy => hfit x (hwitness (x,y) hxy)⟩
  have hfcols (x : X) : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ y, R x y → |f (v x) (w y) - p.eval (w y)| ≤ E := by
    obtain ⟨p,hp,hfit⟩ := hcols x
    exact ⟨p,hp,fun y hxy => hfit y (hwitness (x,y) hxy)⟩
  obtain ⟨P,hP,hPnorm,hPmass⟩ := exists_cartesian_polynomial_field D
    (finiteUniformWeights X) (finiteUniformWeights Y) R
    (finiteUniformWeights_nonneg X) (finiteUniformWeights_sum X)
    (finiteUniformWeights_nonneg Y) (finiteUniformWeights_sum Y)
    v w B gap Bx By η E H hB hgap hBx hBy hη hE hH hv hw hthinX hthinY
    hdensity hloss f hfvals hfrows hfcols
  let W := ((D : ℝ)+1) * (2*B/gap)^D
  let T := Finset.univ.filter (fun c : X × Y => c ∈ F ∧
    |f (v c.1) (w c.2) - eval ![v c.1,w c.2] P| ≤ E*(1+2*W+W^2))
  have hTcount : η^((D+2)^2)/2 ≤ (T.card : ℝ) / N := by
    rw [uniform_grid_relation_density (fun x y => R x y ∧
      |f (v x) (w y) - eval ![v x,w y] P| ≤ E*(1+2*W+W^2))] at hPmass
    simpa only [T, N, R, Prod.mk.eta] using hPmass
  have hcount : N * (η^((D+2)^2)/2) ≤ (T.card : ℝ) := by
    simpa only [mul_comm] using (le_div_iff₀ hN).mp hTcount
  have hsourcefloor : (T.card : ℝ≥0∞) * ENNReal.ofReal θ ≤
      μ {ω | ω ∈ A ∧ cell ω ∈ T} := by
    apply original_grid_subset_mass_lower μ A hA cell hcell T (ENNReal.ofReal θ)
    intro c hc
    exact hfloor c (Finset.mem_filter.mp hc).2.1
  have hfitm : MeasurableSet {ω | ω ∈ A ∧ |f (v (cell ω).1) (w (cell ω).2) -
      eval ![v (cell ω).1,w (cell ω).2] P| ≤ E*(1+2*W+W^2)} := by
    have hm := hA.inter (measurableSet_finite_observation_predicate cell hcell
      (fun c => |f (v c.1) (w c.2) - eval ![v c.1,w c.2] P| ≤ E*(1+2*W+W^2)))
    convert hm using 1
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
  refine ⟨P,hP,hPnorm,hfitm,?_⟩
  calc
    ENNReal.ofReal (θ*N*(η^((D+2)^2)/2)) ≤ ENNReal.ofReal (θ*(T.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_left hcount hθ.le])
    _ = (T.card : ℝ≥0∞) * ENNReal.ofReal θ := by
      rw [ENNReal.ofReal_mul hθ.le]
      simp only [ENNReal.ofReal_natCast, mul_comm]
    _ ≤ μ {ω | ω ∈ A ∧ cell ω ∈ T} := hsourcefloor
    _ ≤ _ := by
      apply measure_mono
      intro ω hω
      exact ⟨hω.1,(Finset.mem_filter.mp hω.2).2.2⟩

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
