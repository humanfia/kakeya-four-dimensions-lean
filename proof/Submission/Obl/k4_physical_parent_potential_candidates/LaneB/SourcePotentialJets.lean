import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceNormalization
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.PotentialJets
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.ZoomJets

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData

noncomputable section

namespace SourceNormalization

def zoomPotential (T j:ℕ) (c u:P2) (s:ℝ) (b cz:Fin 3 → ℝ) (lam:ℝ)
    (P:MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  Analytic.basePullback (Analytic.zoomShift (inverseShift T j c u s b)
    (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam)
    (Broad.parentPotentialPullback T j c u P)

def potentialCenter (s:ℝ) (b cz:Fin 3 → ℝ) : P3 :=
  WithLp.toLp 2 (fun i => s*(cz i-b i))

/-- Exact jet scaling for the actual physical potential after source
normalization and discriminant zoom. -/
theorem iteratedFDeriv_zoomPotential (T j:ℕ) (c u:P2) {s:ℝ} (hs:0<s)
    (b cz:Fin 3 → ℝ) {lam:ℝ} (hlam:lam≠0) (P:MvPolynomial (Fin 3) ℝ) (n:ℕ) (x:P3) :
    iteratedFDeriv ℝ n (fun y:P3 => eval (fun i => y i) (zoomPotential T j c u s b cz lam P)) x =
      (s/lam)^n • iteratedFDeriv ℝ n (fun y:P3 => eval (fun i => y i) P)
        (FubiniZoom.map (potentialCenter s b cz) (s/lam) x) := by
  have hfun : (fun y:P3 => eval (fun i => y i) (zoomPotential T j c u s b cz lam P)) =
      FubiniZoom.pull (fun y:P3 => eval (fun i => y i) P) (potentialCenter s b cz) (s/lam) := by
    funext y
    rw [zoomPotential,Analytic.eval_zoom_potential _ _ _ hlam,normalized_potential T j c u hs,
      eval_potential]
    apply congrArg (fun z:Fin 3 → ℝ => eval z P)
    funext i
    simp only [FubiniZoom.pull,FubiniZoom.map,potentialCenter,PiLp.add_apply,PiLp.smul_apply,
      smul_eq_mul]
    ring
  rw [hfun]
  exact FubiniZoom.iteratedFDeriv_pull isOpen_univ (PotentialJets.contDiff_eval P).contDiffOn
    (by exact_mod_cast le_top) (potentialCenter s b cz) (s/lam) x (mem_univ _)

/-- The point corresponding to an original event under the actual zoomed
physical frame is the same point used by the source potential jet tests. -/
theorem zoomPotential_point (T j:ℕ) (c u:P2) {s:ℝ} (hs:0<s) (b cz:Fin 3 → ℝ)
    {lam:ℝ} (hlam:lam≠0) (B:ℝ) (e:Ev) :
    FubiniZoom.map (potentialCenter s b cz) (s/lam)
      ((Analytic.pointOfCoordinates (Analytic.coordinateMap
        (Analytic.zoomForwardShift (shift T j c u s b) cz lam) (lam • matrix T s) B
        (Analytic.graphPoint e.1 e.2))).1) = packetBase T j c u e := by
  obtain ⟨hb,_⟩ := Analytic.coordinateMap_zoomForward (shift T j c u s b) cz
    (matrix T s) B lam (Analytic.graphPoint e.1 e.2)
  rw [hb]
  ext i
  simp only [FubiniZoom.map,potentialCenter,Analytic.zoomMap,PiLp.add_apply,PiLp.sub_apply,
    PiLp.smul_apply,smul_eq_mul,normalized_base_apply T j c u hs]
  have hsz := hs.ne'
  field_simp
  <;> ring

/-- Uniform pure directional tests of the actual normalized source
potential. The constant is chosen before every source parameter, and the
original signal error `a*zeta` is retained. -/
theorem exists_uniform_zoomed_source_jet_bound (q:ℕ) (hq:2≤q) (r:ℕ) (hr:3≤r) :
    ∃ Cq:ℝ,0<Cq ∧ ∀ {T j:ℕ} {ν:Measure Ln} {B a ζ d:ℝ} {c u:P2} {P0:Po}
      {A:Set Ln} {F H:Set Ev} (source:PhysicalSource q ν B a ζ d T j c u P0 A F H),
      P0.totalDegree≤2 → ∀ {s:ℝ},0<s → ∀ b cz:Fin 3 → ℝ, ∀ {lam:ℝ},1≤lam →
      ∀ l∈source.lineSet, ∀ t∈Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹),
      ∀ x:P3, FubiniZoom.map (potentialCenter s b cz) (s/lam) x=packetBase T j c u (l,t) →
        |iteratedFDeriv ℝ r
          (fun y:P3 => eval (fun i => y i) (zoomPotential T j c u s b cz lam source.Pot)) x
          (fun _ => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l))| ≤ Cq*s^r*a*ζ := by
  obtain ⟨Cq,hCq,hbound⟩ := PhysicalSource.exists_uniform_sharp_actual_time_jet_bound q hq r hr
  refine ⟨Cq,hCq,?_⟩
  intro T j ν B a ζ d c u P0 A F H source hP0 s hs b cz lam hlam l hl t ht x hx
  have hLamPos : 0<lam := by linarith
  have hζ : 0<ζ := source.ε_pos.trans_le source.ε_le
  have ha : 0<a := source.a_pos
  have hscale : (s/lam)^r ≤ s^r := pow_le_pow_left₀ (by positivity)
    (div_le_self hs.le hlam) r
  have hjets := hbound source hP0 l hl t ht
  rw [iteratedFDeriv_zoomPotential T j c u hs b cz hLamPos.ne' source.Pot r x,hx,
    smul_apply,smul_eq_mul,abs_mul,abs_of_pos (pow_pos (div_pos hs hLamPos) r)]
  calc
    _ ≤ s^r*(Cq*a*ζ) := mul_le_mul hscale hjets (abs_nonneg _) (by positivity)
    _ = Cq*s^r*a*ζ := by ring

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
