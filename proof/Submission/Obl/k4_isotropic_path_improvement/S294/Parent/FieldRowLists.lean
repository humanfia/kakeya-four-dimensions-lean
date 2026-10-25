-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.FieldRowLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/FieldRowLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Base-only row lists for the Cartesian field (the `hfield` input of
`Cartesian.frozen_field_long_fits`): the old-core height pieces of a dense root
source (`OldCoreHeights`) and rows Lipschitz in the root physical coordinates
(base, clock signal) give, in a box of any TARGET base, at most `9³` row cells per
kept core/sign entry of one core-depth packet (x1035's
`Qualification.base_row_list_of_height_pieces`). The target box shrinks by the
clock ratio `h_target/h_root` in root coordinates; the height error is
`a_depth/h_root`.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OldCoreHeights
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.BaseRowLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorFrames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentClockState

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set ParentSource ParentSource.Native

noncomputable section

namespace FieldRowLists

/-- An unsheared packet base as a coordinate vector. -/
def baseOf {W : ℕ} (p : PathData W) (b : Fin p.C) (x : Ev) : Fin 3 → ℝ :=
  fun i => unshearedPacketBase p b x i

/-- Unsheared bases of two packets differ by the ratio of their clocks. -/
theorem baseOf_sub {W : ℕ} (p : PathData W) (b b' : Fin p.C) (x y : Ev) :
    baseOf p b x - baseOf p b y =
      (((2 : ℝ) ^ p.T (p.lev b'))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b))⁻¹) •
        (baseOf p b' x - baseOf p b' y) := by
  have h1 := AncestorFrames.scaled_base_difference p b x y
  have h2 := AncestorFrames.scaled_base_difference p b' x y
  have hb : (0 : ℝ) < ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by positivity
  funext i
  have e1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v i) h1
  have e2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v i) h2
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at e1 e2
  simp only [baseOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hb.ne', mul_comm, e1, ← e2]

/-- In three dimensions the Euclidean norm is at most twice the sup norm. -/
theorem euclid_le_two_sup (y : EuclideanSpace ℝ (Fin 3)) :
    ‖y‖ ≤ 2 * ‖(fun i => y i : Fin 3 → ℝ)‖ := by
  set m := ‖(fun i => y i : Fin 3 → ℝ)‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hi (i : Fin 3) : ‖y i‖ ≤ m := by
    have := norm_le_pi_norm (fun i => y i : Fin 3 → ℝ) i
    simpa using this
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_three]
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  have := norm_nonneg (y 0)
  have := norm_nonneg (y 1)
  have := norm_nonneg (y 2)
  nlinarith

section Cores

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K : ℝ} {e R : ℕ} {C : BroadMultiscaleCoreSource d k p original n depth K e R}

/-- The kept core/sign entries of one packet at a core depth. -/
def oldCorePieces (C : BroadMultiscaleCoreSource d k p original n depth K e R) (j : Fin n)
    (b0 : Fin p.C) :
    Finset (Σ v : (C.values j).ActiveValue, ↥(C.cores j v).codes × Bool) :=
  (Set.toFinite {σ : Σ v : (C.values j).ActiveValue, ↥(C.cores j v).codes × Bool |
    σ.1.1.1 = b0}).toFinset

/-- **Base-only row lists of a dense root source.** In a box of half-side
`rad` of any target base, the rows of the incidences of `Eref` meet at most
`9³` row `pm`-cells per kept core/sign entry of the core-depth packet `b0`
containing them, provided the rows are Lipschitz in the ROOT physical
coordinates (base, clock signal). Heights come from `height_pieces`; the
target box shrinks by the clock ratio in root coordinates. -/
theorem field_row_lists_of_old_cores
    {G fineMesh census dimension δ₀' : ℝ} {stop : ℕ}
    (S : DenseRootParentSource C G fineMesh census dimension δ₀' stop)
    (hd : d.Valid) {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ j w, C.source j w ⊆ d.E k w) (hK : 2 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hκK : 3 * p.κ ≤ K) (j : Fin n) (hr : 0 ≤ p.r (depth j)) (target : Fin p.C)
    {ι : Type*} (st : Ev → ι) (Gs : ι → Fin 3 → ℝ)
    (Eref : Set Ev) (hEref : Eref ⊆ S.current) (b0 : Fin p.C)
    (huniq : ∀ x ∈ Eref, ∀ (v : (C.values j).ActiveValue) (ci : ↥(C.cores j v).codes × Bool),
      p.γ v.1.1 = p.γ S.old →
      x ∈ S.current ∩ ((C.values j).inner v.1.1 v.1.2 ∩ (C.cores j v).kept ci) → v.1.1 = b0)
    {Lp ρ rad pm : ℝ} (hLp : 0 ≤ Lp) (hrad : 0 ≤ rad) (hpm : 0 < pm)
    (hreg : ∀ x ∈ Eref, ∀ y ∈ Eref, ‖Gs (st x) - Gs (st y)‖ ≤
      Lp * (‖(Fin.snoc (baseOf p S.old x)
          (clockParentSignal p S.old (d.P k (p.γ S.old)) x) : Fin 4 → ℝ) -
        Fin.snoc (baseOf p S.old y) (clockParentSignal p S.old (d.P k (p.γ S.old)) y)‖ + ρ))
    (hsmall : Lp * ((1 + 2 * (12 * K * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
        (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))))) *
        ((((2 : ℝ) ^ p.T (p.lev target))⁻¹ / ((2 : ℝ) ^ p.T (p.lev S.old))⁻¹) * (2 * rad)) +
        (2 : ℝ) ^ p.T (p.lev S.old) *
          ((2 + G / 2) * (K ^ 14 * (K ^ 6)⁻¹ * ParentSource.δ (d.N k) (p.r (depth j)))) + ρ) ≤
        pm) :
    ∀ c' : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ),
      (F.card : ℝ) ≤ ((oldCorePieces C j b0).card : ℝ) * 9 ^ 3 ∧
      ∀ x ∈ Eref, (∀ i, |baseOf p target x i - c' i| ≤ rad) →
        (fun i => ⌊Gs (st x) i / pm⌋) ∈ F := by
  classical
  intro c'
  set slopeC := 12 * K * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
    (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) with hslopeC
  set hE := (2 + G / 2) * (K ^ 14 * (K ^ 6)⁻¹ * ParentSource.δ (d.N k) (p.r (depth j))) with hhE
  set ht := ((2 : ℝ) ^ p.T (p.lev target))⁻¹ with hht
  set hR := ((2 : ℝ) ^ p.T (p.lev S.old))⁻¹ with hhR
  have hG0 : 0 ≤ G := S.gradient_nonneg
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hNr : 0 ≤ d.N k ^ (2 * δ₀ * d.L) := Real.rpow_nonneg hN.le _
  have hK0 : 0 ≤ K := by linarith
  have hκ0 : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hslope0 : 0 ≤ slopeC := by
    have hKk : 0 ≤ d.K k := by linarith [hd.2.2.1.1 k]
    rw [hslopeC]
    have h1 : 0 ≤ 1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L) := by positivity
    have h2 : 0 ≤ 1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2)) := by
      positivity
    have h3 : 0 ≤ 12 * K * G := by positivity
    exact mul_nonneg (mul_nonneg h3 h1) h2
  have hE0 : 0 ≤ hE := by
    have : 0 ≤ ParentSource.δ (d.N k) (p.r (depth j)) := by unfold ParentSource.δ; positivity
    rw [hhE]; positivity
  have ht0 : 0 < ht := by rw [hht]; positivity
  have hR0 : 0 < hR := by rw [hhR]; positivity
  obtain ⟨hcov, hpair⟩ := S.height_pieces hd hp hHE hK hmax hκK j hr target
  let E : Set Ev := Eref ∩ {x | ∀ i, |baseOf p target x i - c' i| ≤ rad}
  let piece : (Σ v : (C.values j).ActiveValue, ↥(C.cores j v).codes × Bool) → Set Ev :=
    fun σ => (S.current ∩ ((C.values j).inner σ.1.1.1 σ.1.1.2 ∩ (C.cores j σ.1).kept σ.2)) ∩
      {_x | p.γ σ.1.1.1 = p.γ S.old}
  have hcover : ∀ x ∈ E, ∃ i ∈ oldCorePieces C j b0, x ∈ piece i := by
    intro x hx
    obtain ⟨v, ci, hγ, hmem⟩ := hcov x (hEref hx.1)
    refine ⟨⟨v, ci⟩, ?_, hmem, hγ⟩
    simp only [oldCorePieces, Set.Finite.mem_toFinset, mem_ofPred_eq]
    exact huniq x hx.1 v ci hγ hmem
  have hbase : ∀ x ∈ E, ∀ y ∈ E,
      ‖baseOf p S.old x - baseOf p S.old y‖ ≤ ht / hR * (2 * rad) := by
    intro x hx y hy
    rw [baseOf_sub p S.old target x y, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ht0.le hR0.le)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg ht0.le hR0.le)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h1 := hx.2 i
    have h2 := hy.2 i
    rw [Real.norm_eq_abs, Pi.sub_apply]
    calc |baseOf p target x i - baseOf p target y i|
        = |(baseOf p target x i - c' i) - (baseOf p target y i - c' i)| := by ring_nf
      _ ≤ |baseOf p target x i - c' i| + |baseOf p target y i - c' i| := abs_sub _ _
      _ ≤ 2 * rad := by linarith
  have hheight : ∀ i ∈ oldCorePieces C j b0, ∀ x ∈ E, x ∈ piece i → ∀ y ∈ E, y ∈ piece i →
      |clockParentSignal p S.old (d.P k (p.γ S.old)) x -
        clockParentSignal p S.old (d.P k (p.γ S.old)) y| ≤
        (2 : ℝ) ^ p.T (p.lev S.old) * hE + 2 * slopeC *
          ‖baseOf p S.old x - baseOf p S.old y‖ := by
    rintro ⟨v, ci⟩ - x hx hxi y hy hyi
    have hP := hpair v ci hxi.2 x hxi.1 y hyi.1
    have hscale := AncestorFrames.scaled_base_distance p target S.old x y
    have hclock : (2 : ℝ) ^ p.T (p.lev S.old) * hR = 1 := by
      rw [hhR]; exact mul_inv_cancel₀ (by positivity)
    have hsignal : clockParentSignal p S.old (d.P k (p.γ S.old)) x -
        clockParentSignal p S.old (d.P k (p.γ S.old)) y =
        (2 : ℝ) ^ p.T (p.lev S.old) * (MvPolynomial.eval (ParentSource.xp x.1 x.2)
          (d.P k (p.γ S.old)) - MvPolynomial.eval (ParentSource.xp y.1 y.2) (d.P k (p.γ S.old))) := by
      simp only [clockParentSignal]
      ring
    rw [hsignal, abs_mul, abs_of_pos (by positivity)]
    have hU : ‖unshearedPacketBase p S.old x - unshearedPacketBase p S.old y‖ ≤
        2 * ‖baseOf p S.old x - baseOf p S.old y‖ :=
      euclid_le_two_sup (unshearedPacketBase p S.old x - unshearedPacketBase p S.old y)
    calc (2 : ℝ) ^ p.T (p.lev S.old) * |MvPolynomial.eval (ParentSource.xp x.1 x.2)
          (d.P k (p.γ S.old)) - MvPolynomial.eval (ParentSource.xp y.1 y.2) (d.P k (p.γ S.old))|
        ≤ (2 : ℝ) ^ p.T (p.lev S.old) * (hE + slopeC * ht *
            ‖unshearedPacketBase p target x - unshearedPacketBase p target y‖) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (2 : ℝ) ^ p.T (p.lev S.old) * hE + slopeC *
            ((2 : ℝ) ^ p.T (p.lev S.old) * (hR *
              ‖unshearedPacketBase p S.old x - unshearedPacketBase p S.old y‖)) := by
          rw [← hscale]; ring
      _ = (2 : ℝ) ^ p.T (p.lev S.old) * hE + slopeC *
            ‖unshearedPacketBase p S.old x - unshearedPacketBase p S.old y‖ := by
          have key : (2 : ℝ) ^ p.T (p.lev S.old) * (hR *
              ‖unshearedPacketBase p S.old x - unshearedPacketBase p S.old y‖) =
              ‖unshearedPacketBase p S.old x - unshearedPacketBase p S.old y‖ := by
            rw [← mul_assoc, hclock, one_mul]
          rw [key]
      _ ≤ (2 : ℝ) ^ p.T (p.lev S.old) * hE + 2 * slopeC *
            ‖baseOf p S.old x - baseOf p S.old y‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hU hslope0]
  have hphysical : ∀ x ∈ E, ∀ y ∈ E, ‖Gs (st x) - Gs (st y)‖ ≤
      Lp * (‖(Fin.snoc (baseOf p S.old x)
          (clockParentSignal p S.old (d.P k (p.γ S.old)) x) : Fin 4 → ℝ) -
        Fin.snoc (baseOf p S.old y) (clockParentSignal p S.old (d.P k (p.γ S.old)) y)‖ + ρ) :=
    fun x hx y hy => hreg x hx.1 y hy.1
  have hsmall' : Lp * ((1 + 2 * slopeC) * (ht / hR * (2 * rad)) +
      (2 : ℝ) ^ p.T (p.lev S.old) * hE + ρ) ≤ pm := hsmall
  obtain ⟨F, hF, hFmem⟩ := Qualification.base_row_list_of_height_pieces E (baseOf p S.old)
    (clockParentSignal p S.old (d.P k (p.γ S.old))) (fun x => Gs (st x)) (oldCorePieces C j b0)
    piece (by positivity) (by positivity) (by positivity) hLp hpm hcover hbase hheight hphysical
    hsmall'
  exact ⟨F, hF, fun x hx hbox => hFmem x ⟨hx, hbox⟩⟩

/-- One core-depth packet has at most `K¹⁰ · 2K^(3R+18)` kept core/sign entries. -/
theorem oldCorePieces_card_le (j : Fin n) (b0 : Fin p.C) (hK : 0 ≤ K) :
    ((oldCorePieces C j b0).card : ℝ) ≤ K ^ 10 * (2 * K ^ (3 * R + 18)) := by
  classical
  letI : Fintype (C.values j).ActiveValue := Fintype.ofFinite _
  let A : Finset (C.values j).ActiveValue := Finset.univ.filter fun v => v.1.1 = b0
  let T : Finset (Σ v : (C.values j).ActiveValue, ↥(C.cores j v).codes × Bool) :=
    A.sigma fun v => Finset.univ
  have hsub : oldCorePieces C j b0 ⊆ T := by
    intro σ hσ
    simp only [oldCorePieces, Set.Finite.mem_toFinset, mem_ofPred_eq] at hσ
    simp only [T, A, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact hσ
  have hA : (A.card : ℝ) ≤ K ^ 10 := by
    have hinj : A.card ≤ (Finset.univ : Finset (Fin (C.values j).count)).card := by
      apply Finset.card_le_card_of_injOn (fun v => v.1.2)
      · intro v _
        exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro v hv w hw hvw
        have hv' : v.1.1 = b0 := (Finset.mem_filter.mp hv).2
        have hw' : w.1.1 = b0 := (Finset.mem_filter.mp hw).2
        apply Subtype.ext
        exact Prod.ext (hv'.trans hw'.symm) hvw
    rw [Finset.card_univ, Fintype.card_fin] at hinj
    exact (Nat.cast_le.mpr hinj).trans (C.values j).count_le
  have hT : (T.card : ℝ) ≤ K ^ 10 * (2 * K ^ (3 * R + 18)) := by
    simp only [T, Finset.card_sigma, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_coe]
    push_cast
    calc ∑ v ∈ A, ((((C.cores j v).codes.card : ℕ) : ℝ) * 2)
        ≤ ∑ _v ∈ A, (K ^ (3 * R + 18) * 2) :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right
            ((C.cores j v).count_le) (by norm_num)
      _ = (A.card : ℝ) * (K ^ (3 * R + 18) * 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K ^ 10 * (2 * K ^ (3 * R + 18)) := by
          rw [mul_comm (K ^ (3 * R + 18)) 2]
          exact mul_le_mul_of_nonneg_right hA (by positivity)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hT

end Cores

end FieldRowLists

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
