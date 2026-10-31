module

public import ArtGallery.Orthogonal.Hard.RatEq
public import Mathlib

/-!
# Multivariate polynomials with a robust sign test

Values of the copy-nook certificates are polynomials with rational coefficients in a few
parameters (`u`, `G`, `e`).  A polynomial is a list of monomials `(c, [e₀, e₁, …])` standing for
`c · x₀^e₀ · x₁^e₁ ⋯` (`MP.ev`).  The sign test (`MP.nnB`, `MP.posB`) is sound on a box of
parameters: every variable ranges over `[lo, hi]` (`hi = none`: unbounded above); the polynomial is
expanded in the shifted variables `x = lo + (hi − lo) s` (`s ∈ [0, 1]`), resp. `x = lo + s`
(`s ≥ 0`), and bounded below termwise.  A variable flagged *positive* (`lo = 0`, `x > 0`) may be
factored out first, which decides the sign of polynomials vanishing at `x = 0`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

/-! ### Monomials and polynomials -/

/-- The value of a monomial's power product (missing exponents are `0`). -/
noncomputable def monoEval : List ℝ → List ℕ → ℝ
  | _, [] => 1
  | xs, e :: es => xs.headD 0 ^ e * monoEval xs.tail es

/-- Addition of exponent lists (zip-longest). -/
def addExp : List ℕ → List ℕ → List ℕ
  | [], l => l
  | l, [] => l
  | a :: l, b :: l' => (a + b) :: addExp l l'

theorem monoEval_addExp : ∀ (xs : List ℝ) (es fs : List ℕ),
    monoEval xs (addExp es fs) = monoEval xs es * monoEval xs fs
  | xs, [], fs => by simp [addExp, monoEval]
  | xs, e :: es, [] => by simp [addExp, monoEval]
  | xs, e :: es, f :: fs => by
    simp only [addExp, monoEval, monoEval_addExp xs.tail es fs, pow_add]; ring

/-- A monomial `(c, exponents)`. -/
abbrev Mono := ℚ × List ℕ

/-- A polynomial: a list of monomials. -/
abbrev MP := List Mono

/-- The value of a polynomial at `xs`. -/
noncomputable def MP.ev (xs : List ℝ) (p : MP) : ℝ :=
  (p.map fun m => (m.1 : ℝ) * monoEval xs m.2).sum

/-- A constant. -/
def MP.c (q : ℚ) : MP := [(q, [])]

/-- The variable `i`. -/
def MP.var (i : ℕ) : MP := [(1, List.replicate i 0 ++ [1])]

/-- Sum. -/
def MP.add (p q : MP) : MP := p ++ q

/-- Negation. -/
def MP.neg (p : MP) : MP := p.map fun m => (-m.1, m.2)

/-- Difference. -/
def MP.sub (p q : MP) : MP := p.add q.neg

/-- Product. -/
def MP.mul (p q : MP) : MP := p.flatMap fun m => q.map fun m' => (m.1 * m'.1, addExp m.2 m'.2)

/-- Scalar multiple. -/
def MP.smul (a : ℚ) (p : MP) : MP := p.map fun m => (a * m.1, m.2)

theorem MP.ev_nil (xs : List ℝ) : MP.ev xs [] = 0 := by simp [MP.ev]

theorem MP.ev_cons (xs : List ℝ) (m : Mono) (p : MP) :
    MP.ev xs (m :: p) = (m.1 : ℝ) * monoEval xs m.2 + MP.ev xs p := by simp [MP.ev]

@[simp] theorem MP.ev_c (xs : List ℝ) (q : ℚ) : MP.ev xs (MP.c q) = q := by
  simp [MP.c, MP.ev, monoEval]

@[simp] theorem MP.ev_add (xs : List ℝ) (p q : MP) : MP.ev xs (MP.add p q) = MP.ev xs p + MP.ev xs q := by
  simp [MP.add, MP.ev]

@[simp] theorem MP.ev_neg (xs : List ℝ) (p : MP) : MP.ev xs (MP.neg p) = -MP.ev xs p := by
  induction p with
  | nil => simp [MP.neg, MP.ev]
  | cons m p ih =>
    simp only [MP.neg, List.map_cons] at ih ⊢
    rw [MP.ev_cons, MP.ev_cons, ih]; push_cast; ring

@[simp] theorem MP.ev_sub (xs : List ℝ) (p q : MP) : MP.ev xs (MP.sub p q) = MP.ev xs p - MP.ev xs q := by
  simp [MP.sub]; ring

@[simp] theorem MP.ev_smul (xs : List ℝ) (a : ℚ) (p : MP) : MP.ev xs (MP.smul a p) = a * MP.ev xs p := by
  induction p with
  | nil => simp [MP.smul, MP.ev]
  | cons m p ih =>
    simp only [MP.smul, List.map_cons] at ih ⊢
    rw [MP.ev_cons, MP.ev_cons, ih]; push_cast; ring

theorem MP.ev_map_mono_mul (xs : List ℝ) (m : Mono) (q : MP) :
    MP.ev xs (q.map fun m' => (m.1 * m'.1, addExp m.2 m'.2)) = (m.1 : ℝ) * monoEval xs m.2 * MP.ev xs q := by
  induction q with
  | nil => simp [MP.ev]
  | cons m' q ihq =>
    rw [List.map_cons, MP.ev_cons, MP.ev_cons, ihq, monoEval_addExp]; push_cast; ring

@[simp] theorem MP.ev_mul (xs : List ℝ) (p q : MP) : MP.ev xs (MP.mul p q) = MP.ev xs p * MP.ev xs q := by
  induction p with
  | nil => simp [MP.mul, MP.ev]
  | cons m p ih =>
    have e : MP.mul (m :: p) q = (q.map fun m' => (m.1 * m'.1, addExp m.2 m'.2)) ++ MP.mul p q := by
      simp [MP.mul]
    rw [e, show MP.ev xs (_ ++ MP.mul p q) = MP.ev xs (q.map fun m' => (m.1 * m'.1, addExp m.2 m'.2)) +
      MP.ev xs (MP.mul p q) by simp [MP.ev], MP.ev_map_mono_mul, ih, MP.ev_cons]
    ring

theorem monoEval_var : ∀ (i : ℕ) (xs : List ℝ),
    monoEval xs (List.replicate i 0 ++ [1]) = xs.getD i 0
  | 0, xs => by cases xs <;> simp [monoEval]
  | i + 1, xs => by
    cases xs with
    | nil => simp [monoEval, List.replicate_succ, monoEval_var i []]
    | cons x xs => simp [monoEval, List.replicate_succ, monoEval_var i xs]

@[simp] theorem MP.ev_var (xs : List ℝ) (i : ℕ) : MP.ev xs (MP.var i) = xs.getD i 0 := by
  simp [MP.var, MP.ev, monoEval_var]

/-! ### Normal form -/

/-- Drop trailing zero exponents. -/
def trimZ : List ℕ → List ℕ
  | [] => []
  | e :: es => if e = 0 ∧ trimZ es = [] then [] else e :: trimZ es

theorem monoEval_trimZ : ∀ (xs : List ℝ) (es : List ℕ), monoEval xs (trimZ es) = monoEval xs es
  | xs, [] => rfl
  | xs, e :: es => by
    unfold trimZ
    split_ifs with h
    · obtain ⟨rfl, ht⟩ := h
      have := monoEval_trimZ xs.tail es
      rw [ht] at this
      simp only [monoEval, pow_zero, one_mul] at this ⊢
      exact this
    · simp only [monoEval, monoEval_trimZ xs.tail es]

/-- Insert a monomial, merging with a monomial of the same (trimmed) exponents. -/
def insMono (m : Mono) : MP → MP
  | [] => [m]
  | a :: p => if a.2 = m.2 then (a.1 + m.1, a.2) :: p else a :: insMono m p

theorem MP.ev_insMono (xs : List ℝ) (m : Mono) : ∀ p : MP,
    MP.ev xs (insMono m p) = MP.ev xs p + (m.1 : ℝ) * monoEval xs m.2
  | [] => by simp [insMono, MP.ev]
  | a :: p => by
    unfold insMono
    split_ifs with h
    · rw [MP.ev_cons, MP.ev_cons, h]; push_cast; ring
    · rw [MP.ev_cons, MP.ev_cons, MP.ev_insMono xs m p]; ring

/-- The normal form: trimmed exponents, merged monomials, zero coefficients dropped. -/
def MP.norm (p : MP) : MP :=
  (p.foldl (fun acc m => insMono (m.1, trimZ m.2) acc) []).filter (fun m => m.1 != 0)

theorem MP.ev_filter_ne_zero (xs : List ℝ) (p : MP) :
    MP.ev xs (p.filter (fun m => m.1 != 0)) = MP.ev xs p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases h : a.1 = 0
    · simp [List.filter_cons, h, MP.ev_cons, ih]
    · simp [List.filter_cons, h, MP.ev_cons, ih]

theorem MP.ev_foldl (xs : List ℝ) : ∀ (p acc : MP),
    MP.ev xs (p.foldl (fun acc m => insMono (m.1, trimZ m.2) acc) acc) = MP.ev xs acc + MP.ev xs p
  | [], acc => by simp [MP.ev]
  | a :: p, acc => by
    rw [List.foldl_cons, MP.ev_foldl xs p, MP.ev_insMono, monoEval_trimZ, MP.ev_cons]; ring

@[simp] theorem MP.ev_norm (xs : List ℝ) (p : MP) : MP.ev xs (MP.norm p) = MP.ev xs p := by
  rw [MP.norm, MP.ev_filter_ne_zero, MP.ev_foldl]; simp [MP.ev]

/-! ### Substitution -/

/-- The power `q^k`. -/
def MP.pow (q : MP) : ℕ → MP
  | 0 => MP.c 1
  | k + 1 => MP.mul (MP.pow q k) q

@[simp] theorem MP.ev_pow (xs : List ℝ) (q : MP) : ∀ k, MP.ev xs (MP.pow q k) = MP.ev xs q ^ k
  | 0 => by simp [MP.pow]
  | k + 1 => by simp [MP.pow, MP.ev_pow xs q k, pow_succ]

/-- Substitute the polynomials `σ` for the variables of a power product. -/
def substMono (σ : List MP) : List ℕ → MP
  | [] => MP.c 1
  | e :: es => MP.mul (MP.pow (σ.headD (MP.c 0)) e) (substMono σ.tail es)

theorem ev_substMono (ys : List ℝ) : ∀ (σ : List MP) (es : List ℕ),
    MP.ev ys (substMono σ es) = monoEval (σ.map (MP.ev ys)) es
  | σ, [] => by simp [substMono, monoEval]
  | σ, e :: es => by
    simp only [substMono, MP.ev_mul, MP.ev_pow, monoEval, ev_substMono ys σ.tail es]
    congr 1
    · cases σ <;> simp
    · cases σ <;> simp

/-- Substitution `x_i ↦ σ_i` (normalised). -/
def MP.subst (σ : List MP) (p : MP) : MP :=
  MP.norm (p.flatMap fun m => MP.smul m.1 (substMono σ m.2))

theorem MP.ev_subst (ys : List ℝ) (σ : List MP) (p : MP) :
    MP.ev ys (MP.subst σ p) = MP.ev (σ.map (MP.ev ys)) p := by
  rw [MP.subst, MP.ev_norm]
  induction p with
  | nil => simp [MP.ev]
  | cons m p ih =>
    rw [List.flatMap_cons, show MP.ev ys (MP.smul m.1 (substMono σ m.2) ++ p.flatMap _) =
      MP.ev ys (MP.smul m.1 (substMono σ m.2)) + MP.ev ys (p.flatMap fun m => MP.smul m.1 (substMono σ m.2))
      by simp [MP.ev], ih, MP.ev_smul, ev_substMono, MP.ev_cons]

/-! ### The sign test -/

/-- The domain of a variable: `lo ≤ x ≤ hi` (`hi = none`: unbounded); `pos`: moreover `0 < x`
(used with `lo = 0` to factor `x` out). -/
structure VDom where
  lo : ℚ
  hi : Option ℚ
  pos : Bool

/-- A point lies in the domains. -/
def InDom (ds : List VDom) (xs : List ℝ) : Prop :=
  xs.length = ds.length ∧ ∀ i < ds.length, ((ds.getD i ⟨0, none, false⟩).lo : ℝ) ≤ xs.getD i 0 ∧
    (∀ h, (ds.getD i ⟨0, none, false⟩).hi = some h → xs.getD i 0 ≤ h) ∧
    ((ds.getD i ⟨0, none, false⟩).pos = true → 0 < xs.getD i 0)

/-- The shift `x = lo + (hi − lo) s` (bounded), `x = lo + s` (unbounded). -/
def VDom.shift (i : ℕ) (d : VDom) : MP :=
  match d.hi with
  | some h => MP.add (MP.c d.lo) (MP.smul (h - d.lo) (MP.var i))
  | none => MP.add (MP.c d.lo) (MP.var i)

/-- The shifted variables. -/
def shiftVars (ds : List VDom) : List MP := (List.range ds.length).map fun i => (ds.getD i ⟨0, none, false⟩).shift i

/-- The exponent of variable `i` (0 if absent). -/
def expAt (es : List ℕ) (i : ℕ) : ℕ := es.getD i 0

/-- A monomial involves an unbounded variable. -/
def involvesUnb (ds : List VDom) (es : List ℕ) : Bool :=
  (List.range ds.length).any fun i => (ds.getD i ⟨0, none, false⟩).hi.isNone && expAt es i != 0

/-- A lower bound of a shifted monomial's contribution (`s` bounded in `[0, 1]`). -/
def monoLB (ds : List VDom) (m : Mono) : ℚ :=
  if trimZ m.2 = [] then m.1 else if involvesUnb ds m.2 then 0 else min m.1 0

/-- Lower the exponent of variable `i` by `k`. -/
def subExp : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | e :: es, 0, k => (e - k) :: es
  | e :: es, i + 1, k => e :: subExp es i k

theorem monoEval_subExp : ∀ (ss : List ℝ) (es : List ℕ) (i k : ℕ), k ≤ expAt es i →
    monoEval ss es = ss.getD i 0 ^ k * monoEval ss (subExp es i k)
  | ss, [], i, k, h => by
    have : k = 0 := by simp [expAt] at h; omega
    subst this; simp [subExp, monoEval]
  | ss, e :: es, 0, k, h => by
    simp only [expAt, List.getD_cons_zero] at h
    simp only [subExp, monoEval]
    cases ss with
    | nil => simp; rcases Nat.eq_zero_or_pos k with rfl | hk
             · simp
             · rw [zero_pow (by omega), zero_pow hk.ne']; simp
    | cons s ss =>
      simp only [List.headD_cons, List.getD_cons_zero, List.tail_cons]
      rw [show s ^ e = s ^ k * s ^ (e - k) by rw [← pow_add]; congr 1; omega]; ring
  | ss, e :: es, i + 1, k, h => by
    simp only [expAt, List.getD_cons_succ] at h
    simp only [subExp, monoEval]
    rw [monoEval_subExp ss.tail es i k h]
    cases ss with
    | nil => simp; ring
    | cons s ss => simp; ring

/-- The least exponent of variable `i` over the monomials (`0` for the empty polynomial). -/
def minExp (q : MP) (i : ℕ) : ℕ :=
  match q with
  | [] => 0
  | m :: q => q.foldl (fun k m' => min k (expAt m'.2 i)) (expAt m.2 i)

theorem minExp_le (q : MP) (i : ℕ) : ∀ m ∈ q, minExp q i ≤ expAt m.2 i := by
  intro m hm
  cases q with
  | nil => simp at hm
  | cons a q =>
    simp only [minExp]
    have key : ∀ (l : MP) (k : ℕ), l.foldl (fun k m' => min k (expAt m'.2 i)) k ≤ k ∧
        ∀ m ∈ l, l.foldl (fun k m' => min k (expAt m'.2 i)) k ≤ expAt m.2 i := by
      intro l
      induction l with
      | nil => intro k; simp
      | cons b l ih =>
        intro k
        simp only [List.foldl_cons, List.mem_cons]
        obtain ⟨h1, h2⟩ := ih (min k (expAt b.2 i))
        refine ⟨h1.trans (min_le_left _ _), fun m hm => ?_⟩
        rcases hm with rfl | hm
        · exact h1.trans (min_le_right _ _)
        · exact h2 m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact (key q _).1
    · exact (key q _).2 m hm

/-- Divide out the common power of variable `i`. -/
def MP.factorOut (q : MP) (i : ℕ) : MP := q.map fun m => (m.1, subExp m.2 i (minExp q i))

theorem MP.ev_factorOut (ss : List ℝ) (q : MP) (i : ℕ) :
    MP.ev ss q = ss.getD i 0 ^ minExp q i * MP.ev ss (MP.factorOut q i) := by
  have h := minExp_le q i
  unfold MP.factorOut
  generalize minExp q i = k at h ⊢
  induction q with
  | nil => simp [MP.ev]
  | cons m q ih =>
    rw [List.map_cons, MP.ev_cons, MP.ev_cons, ih (fun m hm => h m (List.mem_cons_of_mem _ hm)),
      monoEval_subExp ss m.2 i k (h m List.mem_cons_self)]
    ring

/-- Divide out the common powers of the positive variables (domains with `lo = 0`). -/
def factorPos (ds : List VDom) (q : MP) : MP :=
  (List.range ds.length).foldl (fun q i =>
    if (ds.getD i ⟨0, none, false⟩).pos && (ds.getD i ⟨0, none, false⟩).lo == 0 then
      MP.factorOut q i else q) q

/-- **Robust `0 ≤ p`** on the domains. -/
def MP.nnB (ds : List VDom) (p : MP) : Bool :=
  let q := factorPos ds (MP.subst (shiftVars ds) p)
  (q.all fun m => !(involvesUnb ds m.2) || decide (0 ≤ m.1)) &&
    decide (0 ≤ (q.map (monoLB ds)).sum)

/-- **Robust `0 < p`** on the domains. -/
def MP.posB (ds : List VDom) (p : MP) : Bool :=
  let q := factorPos ds (MP.subst (shiftVars ds) p)
  (q.all fun m => !(involvesUnb ds m.2) || decide (0 ≤ m.1)) &&
    decide (0 < (q.map (monoLB ds)).sum)

/-! ### Soundness of the sign test -/

theorem monoEval_nonneg : ∀ (ss : List ℝ) (es : List ℕ), (∀ s ∈ ss, 0 ≤ s) → 0 ≤ monoEval ss es
  | _, [], _ => by simp [monoEval]
  | ss, e :: es, h => by
    simp only [monoEval]
    have h1 : 0 ≤ ss.headD 0 := by cases ss <;> simp_all
    have h2 : ∀ s ∈ ss.tail, 0 ≤ s := fun s hs => h s (List.mem_of_mem_tail hs)
    exact mul_nonneg (pow_nonneg h1 _) (monoEval_nonneg ss.tail es h2)

theorem monoEval_le_one : ∀ (ss : List ℝ) (es : List ℕ), (∀ s ∈ ss, 0 ≤ s) →
    (∀ i < ss.length, expAt es i ≠ 0 → ss.getD i 0 ≤ 1) → monoEval ss es ≤ 1
  | _, [], _, _ => by simp [monoEval]
  | ss, e :: es, h0, h1 => by
    simp only [monoEval]
    have hh0 : 0 ≤ ss.headD 0 := by cases ss <;> simp_all
    have hpow : ss.headD 0 ^ e ≤ 1 := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp
      · cases ss with
        | nil => simp [zero_pow he.ne']
        | cons s ss =>
          have := h1 0 (by simp) (by simpa [expAt] using he.ne')
          simp only [List.headD_cons]
          simp only [List.getD_cons_zero] at this
          exact pow_le_one₀ (by simpa using hh0) this
    have h0' : ∀ s ∈ ss.tail, 0 ≤ s := fun s hs => h0 s (List.mem_of_mem_tail hs)
    have h1' : ∀ i < ss.tail.length, expAt es i ≠ 0 → ss.tail.getD i 0 ≤ 1 := by
      intro i hi hne
      cases ss with
      | nil => simp at hi
      | cons s ss =>
        have := h1 (i + 1) (by simp at hi ⊢; omega) (by simpa [expAt] using hne)
        simpa using this
    have := monoEval_le_one ss.tail es h0' h1'
    have hn := monoEval_nonneg ss.tail es h0'
    calc ss.headD 0 ^ e * monoEval ss.tail es ≤ 1 * 1 :=
          mul_le_mul hpow this hn zero_le_one
      _ = 1 := by ring

/-- The shifted point: `s = (x − lo)/(hi − lo)` (bounded, `0` if `hi = lo`), `s = x − lo`. -/
noncomputable def shiftPt (ds : List VDom) (xs : List ℝ) : List ℝ :=
  (List.range ds.length).map fun i =>
    let d := ds.getD i ⟨0, none, false⟩
    match d.hi with
    | some h => if (h : ℝ) = d.lo then 0 else (xs.getD i 0 - d.lo) / (h - d.lo)
    | none => xs.getD i 0 - d.lo

theorem shiftPt_spec {ds : List VDom} {xs : List ℝ} (hx : InDom ds xs) :
    (shiftVars ds).map (MP.ev (shiftPt ds xs)) = xs ∧
    (∀ s ∈ shiftPt ds xs, 0 ≤ s) ∧
    (∀ i < (shiftPt ds xs).length, (ds.getD i ⟨0, none, false⟩).hi.isNone = false →
      (shiftPt ds xs).getD i 0 ≤ 1) := by
  obtain ⟨hlen, hdom⟩ := hx
  have hl : (shiftPt ds xs).length = ds.length := by simp [shiftPt]
  have hget : ∀ i < ds.length, (shiftPt ds xs).getD i 0 =
      (match (ds.getD i ⟨0, none, false⟩).hi with
        | some h => if (h : ℝ) = (ds.getD i ⟨0, none, false⟩).lo then 0
            else (xs.getD i 0 - (ds.getD i ⟨0, none, false⟩).lo) / (h - (ds.getD i ⟨0, none, false⟩).lo)
        | none => xs.getD i 0 - (ds.getD i ⟨0, none, false⟩).lo) := by
    intro i hi
    simp [shiftPt, List.getD_eq_getElem?_getD, hi]
  refine ⟨?_, ?_, ?_⟩
  · refine List.ext_getElem (by simp [shiftVars, hlen]) (fun i h1 h2 => ?_)
    have hi : i < ds.length := by simpa [shiftVars] using h1
    simp only [shiftVars, List.getElem_map, List.getElem_range]
    obtain ⟨hlo, hhi, -⟩ := hdom i hi
    have hxi : xs[i] = xs.getD i 0 := by rw [List.getD_eq_getElem _ _ h2]
    rw [hxi]
    unfold VDom.shift
    cases hh : (ds.getD i ⟨0, none, false⟩).hi with
    | none =>
      simp only [MP.ev_add, MP.ev_c, MP.ev_var]
      rw [hget i hi, hh]; ring
    | some h =>
      simp only [MP.ev_add, MP.ev_c, MP.ev_smul, MP.ev_var]
      rw [hget i hi]
      simp only [hh]
      have hle := hhi h hh
      by_cases heq : (h : ℝ) = (ds.getD i ⟨0, none, false⟩).lo
      · simp only [heq, ↓reduceIte, mul_zero, add_zero]; push_cast; linarith
      · simp only [heq, ↓reduceIte]
        have hne : (h : ℝ) - (ds.getD i ⟨0, none, false⟩).lo ≠ 0 := sub_ne_zero.2 heq
        push_cast; field_simp; ring
  · intro s hs
    simp only [shiftPt, List.mem_map, List.mem_range] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    obtain ⟨hlo, hhi, -⟩ := hdom i hi
    cases hh : (ds.getD i ⟨0, none, false⟩).hi with
    | none => simp only [hh]; linarith
    | some h =>
      simp only [hh]
      have hle := hhi h hh
      by_cases heq : (h : ℝ) = (ds.getD i ⟨0, none, false⟩).lo
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        apply div_nonneg <;> linarith [lt_of_le_of_ne (hlo.trans hle) (Ne.symm heq)]
  · intro i hi hb
    rw [hl] at hi
    rw [hget i hi]
    obtain ⟨hlo, hhi, -⟩ := hdom i hi
    cases hh : (ds.getD i ⟨0, none, false⟩).hi with
    | none => rw [hh] at hb; simp at hb
    | some h =>
      simp only [hh]
      have hle := hhi h hh
      by_cases heq : (h : ℝ) = (ds.getD i ⟨0, none, false⟩).lo
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        have hpos : 0 < (h : ℝ) - (ds.getD i ⟨0, none, false⟩).lo := by
          have := lt_of_le_of_ne (hlo.trans hle) (Ne.symm heq); linarith
        rw [div_le_one hpos]; linarith

theorem monoLB_le {ds : List VDom} {ss : List ℝ} (hl : ss.length = ds.length)
    (h0 : ∀ s ∈ ss, 0 ≤ s)
    (h1 : ∀ i < ss.length, (ds.getD i ⟨0, none, false⟩).hi.isNone = false → ss.getD i 0 ≤ 1)
    {m : Mono} (hm : !(involvesUnb ds m.2) || decide (0 ≤ m.1) = true) :
    (monoLB ds m : ℝ) ≤ (m.1 : ℝ) * monoEval ss m.2 := by
  have hn := monoEval_nonneg ss m.2 h0
  unfold monoLB
  split_ifs with ht hu
  · rw [← monoEval_trimZ, ht]; simp [monoEval]
  · simp only [hu, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hm
    push_cast
    exact mul_nonneg (by exact_mod_cast hm) hn
  · have hle : monoEval ss m.2 ≤ 1 := by
      refine monoEval_le_one ss m.2 h0 (fun i hi hne => h1 i hi ?_)
      by_contra hc
      simp only [Bool.not_eq_false, Option.isNone_iff_eq_none] at hc
      apply hu
      simp only [involvesUnb, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        Option.isNone_iff_eq_none, bne_iff_ne, ne_eq]
      exact ⟨i, by omega, by simpa using hc, hne⟩
    rcases le_total 0 m.1 with hc | hc
    · rw [min_eq_right hc]; push_cast
      exact mul_nonneg (by exact_mod_cast hc) hn
    · rw [min_eq_left hc]
      have hc' : (m.1 : ℝ) ≤ 0 := by exact_mod_cast hc
      nlinarith

theorem sum_monoLB_le {ds : List VDom} {ss : List ℝ} (hl : ss.length = ds.length)
    (h0 : ∀ s ∈ ss, 0 ≤ s)
    (h1 : ∀ i < ss.length, (ds.getD i ⟨0, none, false⟩).hi.isNone = false → ss.getD i 0 ≤ 1) :
    ∀ q : MP, (q.all fun m => !(involvesUnb ds m.2) || decide (0 ≤ m.1)) = true →
      (((q.map (monoLB ds)).sum : ℚ) : ℝ) ≤ MP.ev ss q
  | [], _ => by simp [MP.ev]
  | m :: q, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, List.sum_cons, MP.ev_cons]
    push_cast
    have := monoLB_le hl h0 h1 h.1
    have := sum_monoLB_le hl h0 h1 q h.2
    push_cast at this
    linarith

theorem factorPos_spec {ds : List VDom} {ss : List ℝ}
    (hpos : ∀ i < ds.length, (ds.getD i ⟨0, none, false⟩).pos = true →
      (ds.getD i ⟨0, none, false⟩).lo = 0 → 0 < ss.getD i 0) (q : MP) :
    ∃ c : ℝ, 0 < c ∧ MP.ev ss q = c * MP.ev ss (factorPos ds q) := by
  unfold factorPos
  have key : ∀ (l : List ℕ), (∀ i ∈ l, i < ds.length) → ∀ q : MP, ∃ c : ℝ, 0 < c ∧
      MP.ev ss q = c * MP.ev ss (l.foldl (fun q i =>
        if (ds.getD i ⟨0, none, false⟩).pos && (ds.getD i ⟨0, none, false⟩).lo == 0 then
          MP.factorOut q i else q) q) := by
    intro l
    induction l with
    | nil => intro _ q; exact ⟨1, one_pos, by simp⟩
    | cons i l ih =>
      intro hl q
      simp only [List.foldl_cons]
      obtain ⟨c, hc, he⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) (if
        (ds.getD i ⟨0, none, false⟩).pos && (ds.getD i ⟨0, none, false⟩).lo == 0 then
          MP.factorOut q i else q)
      split_ifs at he ⊢ with hb
      · simp only [Bool.and_eq_true, beq_iff_eq] at hb
        have hs := hpos i (hl i List.mem_cons_self) hb.1 hb.2
        refine ⟨ss.getD i 0 ^ minExp q i * c, mul_pos (pow_pos hs _) hc, ?_⟩
        rw [MP.ev_factorOut ss q i, he]; ring
      · exact ⟨c, hc, he⟩
  exact key _ (fun i hi => List.mem_range.1 hi) q

theorem shiftPt_pos {ds : List VDom} {xs : List ℝ} (hx : InDom ds xs) :
    ∀ i < ds.length, (ds.getD i ⟨0, none, false⟩).pos = true →
      (ds.getD i ⟨0, none, false⟩).lo = 0 → 0 < (shiftPt ds xs).getD i 0 := by
  intro i hi hp hlo
  obtain ⟨-, hdom⟩ := hx
  obtain ⟨-, hhi, hpos⟩ := hdom i hi
  have hxp := hpos hp
  have hget : (shiftPt ds xs).getD i 0 = (match (ds.getD i ⟨0, none, false⟩).hi with
        | some h => if (h : ℝ) = (ds.getD i ⟨0, none, false⟩).lo then 0
            else (xs.getD i 0 - (ds.getD i ⟨0, none, false⟩).lo) / (h - (ds.getD i ⟨0, none, false⟩).lo)
        | none => xs.getD i 0 - (ds.getD i ⟨0, none, false⟩).lo) := by
    simp [shiftPt, List.getD_eq_getElem?_getD, hi]
  rw [hget]
  cases hh : (ds.getD i ⟨0, none, false⟩).hi with
  | none => simp only [hh, hlo]; push_cast; linarith
  | some h =>
    simp only [hh, hlo]
    have hle := hhi h hh
    push_cast
    by_cases heq : (h : ℝ) = 0
    · exfalso; linarith
    · simp only [heq, ↓reduceIte, sub_zero]
      exact div_pos hxp (lt_of_lt_of_le hxp hle)

theorem MP.nnB_sound {ds : List VDom} {p : MP} (h : MP.nnB ds p = true) {xs : List ℝ}
    (hx : InDom ds xs) : 0 ≤ MP.ev xs p := by
  obtain ⟨hmap, h0, h1⟩ := shiftPt_spec hx
  have hl : (shiftPt ds xs).length = ds.length := by simp [shiftPt]
  simp only [MP.nnB, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb := sum_monoLB_le hl h0 h1 _ h.1
  obtain ⟨c, hc, he⟩ := factorPos_spec (shiftPt_pos hx) (MP.subst (shiftVars ds) p)
  rw [MP.ev_subst, hmap] at he
  have : (0 : ℝ) ≤ ((((factorPos ds (MP.subst (shiftVars ds) p))).map (monoLB ds)).sum : ℚ) := by
    exact_mod_cast h.2
  rw [he]; exact mul_nonneg hc.le (by linarith)

theorem MP.posB_sound {ds : List VDom} {p : MP} (h : MP.posB ds p = true) {xs : List ℝ}
    (hx : InDom ds xs) : 0 < MP.ev xs p := by
  obtain ⟨hmap, h0, h1⟩ := shiftPt_spec hx
  have hl : (shiftPt ds xs).length = ds.length := by simp [shiftPt]
  simp only [MP.posB, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb := sum_monoLB_le hl h0 h1 _ h.1
  obtain ⟨c, hc, he⟩ := factorPos_spec (shiftPt_pos hx) (MP.subst (shiftVars ds) p)
  rw [MP.ev_subst, hmap] at he
  have : (0 : ℝ) < ((((factorPos ds (MP.subst (shiftVars ds) p))).map (monoLB ds)).sum : ℚ) := by
    exact_mod_cast h.2
  rw [he]; exact mul_pos hc (by linarith)

/-! ### Subdivision -/

/-- The lower (`b = false`) or upper (`b = true`) half of a bounded domain. -/
def VDom.half (d : VDom) (b : Bool) : VDom :=
  match d.hi with
  | some h => if b then ⟨(d.lo + h) / 2, some h, d.pos⟩ else ⟨d.lo, some ((d.lo + h) / 2), d.pos⟩
  | none => d

/-- Halve the domain of variable `i`. -/
def halfDom (ds : List VDom) (i : ℕ) (b : Bool) : List VDom :=
  (List.range ds.length).map fun j =>
    if j = i then (ds.getD j ⟨0, none, false⟩).half b else ds.getD j ⟨0, none, false⟩

theorem halfDom_getD (ds : List VDom) (i : ℕ) (b : Bool) {j : ℕ} (hj : j < ds.length) :
    (halfDom ds i b).getD j ⟨0, none, false⟩ =
      if j = i then (ds.getD j ⟨0, none, false⟩).half b else ds.getD j ⟨0, none, false⟩ := by
  simp [halfDom, List.getD_eq_getElem?_getD, hj]

/-- A point of the domains lies in one of the halves. -/
theorem inDom_half {ds : List VDom} {xs : List ℝ} (hx : InDom ds xs) (i : ℕ) :
    InDom (halfDom ds i false) xs ∨ InDom (halfDom ds i true) xs := by
  obtain ⟨hlen, hdom⟩ := hx
  have hl : ∀ b, (halfDom ds i b).length = ds.length := fun b => by simp [halfDom]
  -- the other variables keep their domains
  have other : ∀ b, (∀ (hi : i < ds.length),
      ((((ds.getD i ⟨0, none, false⟩).half b).lo : ℝ) ≤ xs.getD i 0 ∧
        (∀ h, ((ds.getD i ⟨0, none, false⟩).half b).hi = some h → xs.getD i 0 ≤ h) ∧
        (((ds.getD i ⟨0, none, false⟩).half b).pos = true → 0 < xs.getD i 0))) →
      InDom (halfDom ds i b) xs := by
    intro b hb
    refine ⟨by rw [hl]; exact hlen, fun j hj => ?_⟩
    rw [hl] at hj
    rw [halfDom_getD ds i b hj]
    split_ifs with hji
    · subst hji; exact hb hj
    · exact hdom j hj
  by_cases hi : i < ds.length
  · obtain ⟨hlo, hhi, hpos⟩ := hdom i hi
    cases hh : (ds.getD i ⟨0, none, false⟩).hi with
    | none =>
      left
      refine other false (fun _ => ?_)
      simp only [VDom.half, hh]
      exact ⟨hlo, fun h hh' => by simp at hh', hpos⟩
    | some h =>
      have hle := hhi h hh
      rcases le_total (xs.getD i 0) ((((ds.getD i ⟨0, none, false⟩).lo + h) / 2 : ℚ) : ℝ) with hc | hc
      · left
        refine other false (fun _ => ?_)
        simp only [VDom.half, hh, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hlo, fun h' hh' => by simp only [Option.some.injEq] at hh'; rw [← hh']; exact hc, hpos⟩
      · right
        refine other true (fun _ => ?_)
        simp only [VDom.half, hh, ↓reduceIte]
        exact ⟨hc, fun h' hh' => by simp only [Option.some.injEq] at hh'; rw [← hh']; exact hle, hpos⟩
  · left
    exact other false (fun h => absurd h hi)

/-- **Robust `0 ≤ p` with subdivision**: the test of `MP.nnB`, or both halves of the domain of a
variable (cycling through the variables) at depth `k`. -/
def MP.nnS (ds : List VDom) (p : MP) : ℕ → Bool
  | 0 => MP.nnB ds p
  | k + 1 => MP.nnB ds p ||
      (MP.nnS (halfDom ds (k % ds.length) false) p k && MP.nnS (halfDom ds (k % ds.length) true) p k)

/-- **Robust `0 < p` with subdivision.** -/
def MP.posS (ds : List VDom) (p : MP) : ℕ → Bool
  | 0 => MP.posB ds p
  | k + 1 => MP.posB ds p ||
      (MP.posS (halfDom ds (k % ds.length) false) p k && MP.posS (halfDom ds (k % ds.length) true) p k)

theorem MP.nnS_sound {p : MP} : ∀ {k : ℕ} {ds : List VDom}, MP.nnS ds p k = true →
    ∀ {xs : List ℝ}, InDom ds xs → 0 ≤ MP.ev xs p
  | 0, ds, h, xs, hx => MP.nnB_sound h hx
  | k + 1, ds, h, xs, hx => by
    simp only [MP.nnS, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact MP.nnB_sound h hx
    · rcases inDom_half hx (k % ds.length) with hx' | hx'
      · exact MP.nnS_sound h1 hx'
      · exact MP.nnS_sound h2 hx'

theorem MP.posS_sound {p : MP} : ∀ {k : ℕ} {ds : List VDom}, MP.posS ds p k = true →
    ∀ {xs : List ℝ}, InDom ds xs → 0 < MP.ev xs p
  | 0, ds, h, xs, hx => MP.posB_sound h hx
  | k + 1, ds, h, xs, hx => by
    simp only [MP.posS, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact MP.posB_sound h hx
    · rcases inDom_half hx (k % ds.length) with hx' | hx'
      · exact MP.posS_sound h1 hx'
      · exact MP.posS_sound h2 hx'

end

end ArtGallery.Orthogonal.Hard
