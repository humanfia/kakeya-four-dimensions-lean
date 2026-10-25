-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Stability
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Extraction
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Factoring
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Parameters
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# Quantitative convex factorization

A finite-power variational selection stabilizes the convex-count coefficient.
Saturated convex containers are enclosed by prisms using transverse determinants,
rounded to common widths, and pruned using disjoint assigned tube blocks.
All fixed and geometric-grid losses are absorbed into the prescribed exponent.
-/

open WangZahlLot.Obl.wz_concentrated_convex_factorization
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective)
open Set MeasureTheory

theorem WangZahlLot.wz_concentrated_convex_factorization : ∀ C ν:ℝ, (fun (B:Set (EuclideanSpace ℝ (Fin 3))) => (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) => (fun (o:ℝ → ENNReal) => (fun (T:ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) => (fun (N:ℝ → ℝ → ℝ → (n:ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop) => (fun (F:ℝ → ℝ → ℝ → ℝ → ℝ → (n:ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop) => 0 < C → 0 < ν → ∃ d:ℝ, 0 < d∧∀ δ:ℝ, 0 < δ → δ ≤ (1/100:ℝ) → δ ≤ d → ∀ m:ℝ, 1 ≤ m → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖=1) → (∀ i, T δ (x i) (v i)⊆B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i)∩T δ (x j) (v j)) ≤ (1/2:ENNReal)*μ (T δ (x i) (v i))) → (n:ℝ)*δ^4 ≤ C → (∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {i | T δ (x i) (v i)⊆U}:ℝ)*δ^2) ≤ o m*μ U) → ∃ a b:ℝ, δ ≤ a∧a ≤ b∧b ≤ 2∧F ν δ a b m n x v) (fun ν δ a b m n x v => ∃ (k:ℕ) (g:Fin k → Fin n), Function.Injective g∧0 < k∧δ^ν*n ≤ k∧∃ c:ℝ, 1 ≤ c∧c ≤ m∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {i | T δ (x (g i)) (v (g i))⊆U}:ℝ)*δ^2) ≤ o c*μ U)∧∃ (q:ℕ), 0 < q∧∃ W:Fin q → Set (EuclideanSpace ℝ (Fin 3)), (∀ j, ∃ e:AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)), W j=e '' {p:(EuclideanSpace ℝ (Fin 3)) | |p 0| ≤ a∧|p 1| ≤ b∧|p 2| ≤ 2})∧(∀ i, ∃ j, T δ (x (g i)) (v (g i))⊆W j)∧(∀ i, (Set.ncard {j | T δ (x (g i)) (v (g i))⊆W j}:ℝ) ≤ δ^(-ν))∧(∀ j j', (Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j}:ℝ) ≤ δ^(-ν)*(Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j'}:ℝ))∧(∀ j, δ^ν*c*a*b ≤ (Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j}:ℝ)*δ^2)∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {j | W j⊆U}:ℝ)*a*b) ≤ o (δ^(-ν))*μ U)∧(∀ j, ∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j∧T δ (x (g i)) (v (g i))⊆U}:ℝ)*a*b) ≤ o (δ^(-ν)*(Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j}:ℝ))*μ U))) (fun θ ζ δ n x v => ∀ (k:ℕ) (g:Fin k → Fin n), Function.Injective g → δ^θ*n ≤ k → ¬ ∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o (Set.ncard {i | T δ (x (g i)) (v (g i))⊆U}:ℝ) ≤ o (δ^(-ζ)*k)*μ U)) (fun δ x v => Metric.thickening δ (segment ℝ x (x+v)))) (ENNReal.ofReal)) (MeasureTheory.volume)) (Metric.ball (0:(EuclideanSpace ℝ (Fin 3))) 1) := by
  classical
  intro C ν hC hν
  obtain ⟨p, d, hp, hd, hparam⟩ := choose_parameters C ν hC hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδ100 hδd m hm n x v hn hv hball hover hnC hupper
  obtain ⟨hhalf, hCd, hpower, hgrid, hretain, herror⟩ := hparam δ hδ hδd
  have hδ1 : δ ≤ 1 := by linarith
  let ε := ν / 20
  let T := fun i => Tube δ (x i) (v i)
  let K : ℝ := 2 ^ p
  let r := δ ^ (-ε)
  let B := 1024 * K * r ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hr1 : 1 ≤ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hK1 : 1 ≤ K := one_le_pow₀ (by norm_num)
  have hB1 : 1 ≤ B := by
    have hh := mul_le_mul hK1 (one_le_pow₀ hr1 (n := 2)) (by norm_num) (by linarith : 0 ≤ K)
    dsimp only [B]
    nlinarith
  have hS₀ : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hu : Upper T (δ ^ 2) Finset.univ m := by
    intro U hU
    rw [count_univ]
    exact hupper U hU
  have hf : ∀ R ⊆ (Finset.univ : Finset (Fin n)), R.Nonempty → 1 ≤ coefficient T (δ ^ 2) R := by
    intro R hR _
    exact one_le_coefficient hm (hu.subset (sq_nonneg δ) hR)
  have hfB : coefficient T (δ ^ 2) Finset.univ ≤ δ ^ (-(6 : ℝ)) := by
    have hh := tube_coefficient_bound hδ hδ1 x v Finset.univ hS₀
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    exact hh.trans (polynomial_coefficient_bound hδ hCd hnC)
  obtain ⟨S, hSsub, hSne, hSret, hstable⟩ := stable_subfamily Finset.univ hS₀
    (fun R => coefficient T (δ ^ 2) R) hf p hp (Real.rpow_nonneg hδ.le ε) hfB hpower
  simp only [Finset.card_univ, Fintype.card_fin] at hSret
  have huS := hu.subset (sq_nonneg δ) hSsub
  obtain ⟨a, b, R, N, W, ha, hab, hb, hRS, hRne, hN, hRret, hshape, hW, hcover, hdegree, hsat⟩ :=
    extract_cover hδ hδ1 hm hr1 (by dsimp [K]; positivity : 0 < K) p hgrid x v S hSne
      (fun i _ => hv i) (fun i _ => hball i) huS hstable
  let c := coefficient T (δ ^ 2) S
  have hc1 : 1 ≤ c := one_le_coefficient hm huS
  have hcm : c ≤ m := coefficient_le hm huS
  have huR : Upper T (δ ^ 2) R c := (coefficient_upper (sq_nonneg δ) hm huS).subset (sq_nonneg δ) hRS
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have herr : 128 * B ^ 2 ≤ δ ^ (-ν) := herror
  have h64 : 64 * B ≤ δ ^ (-ν) := by nlinarith
  have h32 : 32 * B ≤ δ ^ (-ν) := by nlinarith
  have h2 : 2 * B ≤ δ ^ (-ν) := by nlinarith
  have hkeep : δ ^ ν * (n : ℝ) ≤ R.card := by
    let L : ℝ := 4 * (p + 1 : ℝ) ^ 2
    have hL : 0 < L := by dsimp [L]; positivity
    apply (mul_le_mul_iff_right₀ hL).mp
    calc
      L * (δ ^ ν * (n : ℝ)) = (δ ^ ν * L) * n := by ring
      _ ≤ δ ^ ε * n := mul_le_mul_of_nonneg_right hretain (Nat.cast_nonneg _)
      _ ≤ S.card := hSret
      _ ≤ L * R.card := hRret
  obtain ⟨hbalance, habove, hbelow⟩ := factor_bounds W (sq_pos_of_pos hδ)
    (hδ.le.trans ha) (hδ.le.trans (ha.trans hab)) (by linarith : 0 < c)
    (by linarith : 0 ≤ B) huR hW hdegree hsat
  refine ⟨a, b, ha, hab, hb, R.card, enumerate R, enumerate_injective R,
    Finset.card_pos.mpr hRne, hkeep, c, hc1, hcm, ?_, N, hN, W, hshape, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    change ENNReal.ofReal ((ncard {i | T (enumerate R i) ⊆ U} : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal c * volume U
    rw [count_enumerate]
    exact huR U hU
  · intro i
    exact hcover (enumerate R i) (enumerate_mem R i)
  · intro i
    exact (hdegree (enumerate R i) (enumerate_mem R i)).trans h64
  · intro j j'
    change (ncard {i | T (enumerate R i) ⊆ W j} : ℝ) ≤
      δ ^ (-ν) * (ncard {i | T (enumerate R i) ⊆ W j'} : ℝ)
    rw [count_enumerate, count_enumerate]
    exact (hbalance j j').trans (mul_le_mul_of_nonneg_right h32 (Nat.cast_nonneg _))
  · intro j
    change δ ^ ν * c * a * b ≤ (ncard {i | T (enumerate R i) ⊆ W j} : ℝ) * δ ^ 2
    rw [count_enumerate]
    have hs := hsat j
    have hmult := mul_le_mul_of_nonneg_right h2
      (mul_nonneg (Nat.cast_nonneg (count T R (W j))) (sq_nonneg δ))
    have hh : c * a * b ≤ δ ^ (-ν) * ((count T R (W j) : ℝ) * δ ^ 2) := by
      nlinarith
    have he : δ ^ ν * δ ^ (-ν) = 1 := by rw [← Real.rpow_add hδ]; simp
    calc
      δ ^ ν * c * a * b = δ ^ ν * (c * a * b) := by ring
      _ ≤ δ ^ ν * (δ ^ (-ν) * ((count T R (W j) : ℝ) * δ ^ 2)) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hδ.le _)
      _ = (count T R (W j) : ℝ) * δ ^ 2 := by rw [← mul_assoc, he, one_mul]
  · intro U hU
    have hh := (habove.mono herr) U hU
    simpa only [count_univ, mul_assoc] using hh
  · intro j U hU
    change ENNReal.ofReal ((ncard {i | T (enumerate R i) ⊆ W j ∧ T (enumerate R i) ⊆ U} : ℝ) * a * b) ≤
      ENNReal.ofReal (δ ^ (-ν) * (ncard {i | T (enumerate R i) ⊆ W j} : ℝ)) * volume U
    rw [count_filter_enumerate, count_enumerate]
    have hh := ((hbelow j).mono (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))) U hU
    simpa only [mul_assoc] using hh
