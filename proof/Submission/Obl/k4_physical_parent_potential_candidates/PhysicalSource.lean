import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalGeometry

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open scoped ENNReal

noncomputable section

/-- The actual witnesses supplied by the frozen physical packet. -/
structure PhysicalSource (q : ℕ) (ν : Measure Ln) (B a ζ d : ℝ)
    (T j : ℕ) (c u : P2) (P0 : Po) (A : Set Ln) (F H : Set Ev) where
  K : ℝ
  ε : ℝ
  S : Set Ev
  Pot : MvPolynomial (Fin 3) ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ ζ
  ε_clock : ε ≤ (a / ((2:ℝ)^T)⁻¹)*ζ
  a_pos : 0 < a
  a_le : a ≤ K*((2:ℝ)^T)⁻¹
  clock_le : ((2:ℝ)^T)⁻¹ ≤ ζ
  K_two : 2 ≤ K
  measurable_S : MeasurableSet S
  subset_S : S ⊆ H ∩ F
  reference_pos : 0 < ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A
  mass_floor : (ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A)/ENNReal.ofReal K ≤
    ((ν.prod volume).restrict S) univ
  degree : Pot.totalDegree ≤ q
  coeff : ∀ e, |Pot.coeff e| ≤ K*((2:ℝ)^T)⁻¹
  point_bounds : ∀ e ∈ S,
    ‖packetBase T j c u e‖ ≤ K ∧ ‖v e.1‖ ≤ K ∧
    (∀ t ∈ Icc (0:ℝ) 1,
      |eval (xp e.1 t) P0| ≤ K ∧
      |eval (xp e.1 t) (pderiv 3 P0)| ≤ K*B ∧
      |eval (xp e.1 t) (pderiv 3 (pderiv 3 P0))| ≤ K*B^2) ∧
    B/K ≤ |eval (xp e.1 e.2) (pderiv 3 P0)| ∧
    (∀ t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹),
      |(eval (xp e.1 t) P0 - eval (fun i => packetBase T j c u (e.1,t) i) Pot) -
        ownIntercept T j c u P0 Pot e.1| ≤ a*ζ)
  breadth : ∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
    ((ν.prod volume).restrict S)
      {e | physicalCode (packetBase T j c u) (fun e => packetSignal P0 e/a) ε e = k ∧
        |inner ℝ n (v e.1)-t| ≤ K^(-100:ℝ)} ≤
      (1/1000000000000:ENNReal)*((ν.prod volume).restrict S)
        {e | physicalCode (packetBase T j c u) (fun e => packetSignal P0 e/a) ε e = k}
  base_cap : ∀ U : Set P3, MeasurableSet U →
    ((ν.prod volume).restrict S) {e | packetBase T j c u e ∈ U} ≤
      ENNReal.ofReal K*(ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A)*volume U
  scalar_cap : ∀ w : ℝ, ε ≤ w → w ≤ 1 → ∀ U : Set P3, MeasurableSet U →
    ∀ f : P3 → ℝ, Measurable f →
      ((ν.prod volume).restrict S)
        {e | packetBase T j c u e ∈ U ∧ |packetSignal P0 e/a-f (packetBase T j c u e)| ≤ w} ≤
        ENNReal.ofReal (K*w^d)*(ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A)*volume U
  census : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
    K^100*((2:ℝ)^T)⁻¹*p ≤ a*w →
    Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k} ∧
    (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k}).ncard:ℝ) ≤
      K/(p^3*w^d)

/-- Bundle the packet witnesses without changing their signal, source or prior. -/
theorem physical_source_of_packet
    {q T j : ℕ} {precision loss Nk L d gain κ B r : ℝ} {ν : Measure Ln}
    {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
    (hpacket : PhysicalPotentialPacket q precision loss Nk L d gain κ ν B r T j c u P0 A F H) :
    ∃ source : PhysicalSource q ν B (δ Nk r) (δ Nk (precision*gain*L)) d T j c u P0 A F H,
      κ ≤ source.K ∧ source.K ≤ Nk^(loss*gain*L) := by
  rcases hpacket with ⟨K, ε, S, Pot, hε, hεζ, hεclock, ha, haK, hhζ, hK, hκ,
    hKN, hSm, hSsub, href, hmass, hdeg, hcoeff, hpoint, hbreadth, hbase, hscalar, hcensus⟩
  refine ⟨{
    K := K
    ε := ε
    S := S
    Pot := Pot
    ε_pos := hε
    ε_le := hεζ
    ε_clock := hεclock
    a_pos := ha
    a_le := haK
    clock_le := hhζ
    K_two := hK
    measurable_S := hSm
    subset_S := hSsub
    reference_pos := href
    mass_floor := hmass
    degree := hdeg
    coeff := hcoeff
    point_bounds := ?_
    breadth := hbreadth
    base_cap := hbase
    scalar_cap := hscalar
    census := hcensus }, hκ, hKN⟩
  exact hpoint

end

end Submission.Obl.k4_physical_parent_potential_candidates

