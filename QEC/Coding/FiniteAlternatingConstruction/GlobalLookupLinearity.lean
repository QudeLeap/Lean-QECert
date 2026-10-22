import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoderZero

/-!
# Linearity of the literal complete-table global lookup on its image

The proof follows the zero-updated branch BEFORE the one-updated branch of
`wordsOn`. It neither changes the table nor chooses an alternative section.
This is a project-derived internal API for selector analysis, not a proof of
local-first linearity, reachable-history exactness or the BDL26 stability claim
(paper.tex:3404–3484). Off-image inputs retain the original zero default.
-/
namespace QEC.Coding.BDL26GlobalLookupLinearity

open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators

abbrev Bit := ZMod 2

private theorem bit_cases (c : Bit) : c=0 ∨ c=1 :=
  (by decide : ∀ a : Bit, a=0 ∨ a=1) c

private theorem word_add_self {I : Type} (a : Word Bit I) : a+a=0 := by
  funext i
  have h : ∀ c : Bit, c+c=0 := by decide
  exact h (a i)

/-- Strict zero-before-one comparison in precisely the supplied coordinate list. -/
def Before {I : Type} : List I → Word Bit I → Word Bit I → Prop
  | [], _, _ => False
  | q::qs, a, b => (a q=0 ∧ b q=1) ∨ (a q=b q ∧ Before qs a b)

private theorem before_update {I : Type} [DecidableEq I] (qs : List I)
    (q : I) (hq : q∉qs) (a b : Word Bit I) (x y : Bit) :
    Before qs (Function.update a q x) (Function.update b q y) ↔ Before qs a b := by
  revert hq
  induction qs with
  | nil => intro hq; rfl
  | cons r rs ih =>
      intro hq
      have hr : r≠q := by intro h; subst r; exact hq (by simp)
      have hqr : q∉rs := fun h => hq (List.mem_cons_of_mem r h)
      simp only [Before, Function.update_of_ne hr, ih hqr]

private theorem search_map {I J : Type} (accept : J → Bool) (f : I → J)
    (xs : List I) : search accept (xs.map f)=
      (search (fun a => accept (f a)) xs).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : accept (f a)=true <;> simp [search,h,ih]

private theorem search_append {I : Type} (accept : I → Bool) (xs ys : List I) :
    search accept (xs++ys)=
      match search accept xs with | some a => some a | none => search accept ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : accept a=true <;> simp [search,h,ih]

private theorem search_wordsOn_cons {I : Type} [DecidableEq I]
    (accept : Word Bit I → Bool) (q : I) (qs : List I) :
    search accept (wordsOn (q::qs))=
      match search (fun a => accept (Function.update a q 0)) (wordsOn qs) with
      | some a => some (Function.update a q 0)
      | none => (search (fun a => accept (Function.update a q 1)) (wordsOn qs)).map
          (fun a => Function.update a q 1) := by
  rw [wordsOn,search_append,search_map,search_map]
  cases search (fun a => accept (Function.update a q 0)) (wordsOn qs) <;> rfl

private theorem rejected_of_search_none {I : Type} (accept : I → Bool)
    (xs : List I) (hn : search accept xs=none) (a : I) (ha : a∈xs) :
    accept a≠true := by
  intro ht
  obtain ⟨b,hb⟩ := search_complete accept xs ⟨a,ha,ht⟩
  rw [hn] at hb
  cases hb

/-- The literal search is minimal for its actual recursive table order.
No weight, owner filter, Gaussian elimination or choice certificate occurs. -/
theorem search_wordsOn_minimal {I : Type} [DecidableEq I]
    (qs : List I) (hn : qs.Nodup) (accept : Word Bit I → Bool)
    (r : Word Bit I) (hr : search accept (wordsOn qs)=some r) :
    ∀ a∈wordsOn qs, accept a=true → ¬Before qs a r := by
  revert hr r accept hn
  induction qs with
  | nil => intro hn accept r hr a ha hp hb; exact hb
  | cons q qs ih =>
      intro hn accept r hr
      have hq : q∉qs := (List.nodup_cons.mp hn).1
      have htail : qs.Nodup := (List.nodup_cons.mp hn).2
      rw [search_wordsOn_cons] at hr
      cases hz : search (fun a => accept (Function.update a q 0)) (wordsOn qs) with
      | some z =>
          simp only [hz] at hr
          have er : Function.update z q 0=r := Option.some.inj hr
          subst r
          intro a ha hp hb
          change a∈(wordsOn qs).map (fun b => Function.update b q 0) ++
            (wordsOn qs).map (fun b => Function.update b q 1) at ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
            have hbefore : Before qs b z := by
              have ht : Before qs (Function.update b q 0) (Function.update z q 0) := by
                simpa only [Before,Function.update_self,eq_self_iff_true,zero_ne_one,and_false,false_and,
                  false_or,true_and] using hb
              exact (before_update qs q hq b z 0 0).mp ht
            exact ih htail _ z hz b hbmem hp hbefore
          · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
            simpa only [Before,Function.update_self,one_ne_zero,zero_ne_one,
              false_and,and_false,false_or] using hb
      | none =>
          simp only [hz] at hr
          cases ho : search (fun a => accept (Function.update a q 1)) (wordsOn qs) with
          | none => simp only [ho,Option.map_none] at hr; cases hr
          | some z =>
              simp only [ho,Option.map_some] at hr
              have er : Function.update z q 1=r := Option.some.inj hr
              subst r
              intro a ha hp hb
              change a∈(wordsOn qs).map (fun b => Function.update b q 0) ++
                (wordsOn qs).map (fun b => Function.update b q 1) at ha
              rcases List.mem_append.mp ha with ha | ha
              · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
                exact rejected_of_search_none _ _ hz b hbmem hp
              · obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
                have hbefore : Before qs b z := by
                  have ht : Before qs (Function.update b q 1) (Function.update z q 1) := by
                    simpa only [Before,Function.update_self,eq_self_iff_true,one_ne_zero,false_and,
                      false_or,true_and] using hb
                  exact (before_update qs q hq b z 1 1).mp ht
                exact ih htail _ z ho b hbmem hp hbefore

/-- A nonzero binary word has a first-one witness in the literal list order.
Adding it lowers ANY word whose value at that witness is one. -/
theorem first_one_or_zero {I : Type} (qs : List I) (k : Word Bit I) :
    (∀ q∈qs, k q=0) ∨
      ∃ q∈qs, k q=1 ∧ ∀ r : Word Bit I, r q=1 → Before qs (r+k) r := by
  induction qs with
  | nil => exact Or.inl (by intro q h; cases h)
  | cons q qs ih =>
      rcases bit_cases (k q) with hk | hk
      · rcases ih with hzero | ⟨p,hp,hkp,hbefore⟩
        · apply Or.inl
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hk
          · exact hzero p hp
        · refine Or.inr ⟨p,List.mem_cons_of_mem q hp,hkp,?_⟩
          intro r hr
          exact Or.inr ⟨by simp only [Pi.add_apply,hk,add_zero],hbefore r hr⟩
      · refine Or.inr ⟨q,List.mem_cons_self,hk,?_⟩
        intro r hr
        exact Or.inl ⟨by change r q+k q=0; rw [hr,hk]; decide,hr⟩

variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

/-- EXACT original unfiltered search, including its off-image zero default. -/
def G (L : Word Bit A →ₗ[Bit] Word Bit B) (s : Word Bit B) : Word Bit A :=
  (search (fun e => decide (L e=s)) (allWords A)).getD 0

/-- Actual image membership forces successful complete-table search. -/
theorem global_search_success (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) :
    ∃ e, search (fun a => decide (L a=s)) (allWords A)=some e := by
  obtain ⟨a,ha⟩ := hs
  exact search_complete _ _ ⟨a,mem_allWords A a,by simpa using ha⟩

/-- Full preimage identity, with empty and noninjective carriers allowed. -/
theorem global_preimage (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) : L (G L s)=s := by
  obtain ⟨e,he⟩ := global_search_success L s hs
  have hp := (search_sound _ _ _ he).2
  simpa only [G,he,Option.getD_some,decide_eq_true_eq] using hp

/-- Zero normalization follows from the REAL zero-first table, not linear choice. -/
theorem global_zero (L : Word Bit A →ₗ[Bit] Word Bit B) : G L 0=0 := by
  obtain ⟨tail,htail⟩ := allWords_zero_first A
  simp [G,htail,search]

/-- The default is retained outside the image, with no additivity claim there. -/
theorem global_off_image (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∉LinearMap.range L) : G L s=0 := by
  cases he : search (fun a => decide (L a=s)) (allWords A) with
  | none => simp only [G,he,Option.getD_none]
  | some a =>
      have ha : L a=s := of_decide_eq_true (search_sound _ _ _ he).2
      exact False.elim (hs ⟨a,ha⟩)

/-- Every actual returned representative is lex-minimal in its syndrome coset. -/
theorem global_minimal (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) :
    ∀ a : Word Bit A, L a=s → ¬Before (coordinates A) a (G L s) := by
  obtain ⟨e,he⟩ := global_search_success L s hs
  have hn : (coordinates A).Nodup := by
    letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
    change (Finset.univ.sort : List A).Nodup
    exact Finset.sort_nodup _ _
  have hm := search_wordsOn_minimal (coordinates A) hn
    (fun a => decide (L a=s)) e he
  intro a ha
  simpa only [G,he,Option.getD_some] using
    hm a (mem_allWords A a) (by simpa using ha)

/-- Complete additivity on syndromes of arbitrary ORIGINAL input words. -/
theorem global_add_words (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a b : Word Bit A) : G L (L a+L b)=G L (L a)+G L (L b) := by
  let r := G L (L a)
  let t := G L (L b)
  let u := G L (L a+L b)
  have hr : L r=L a := global_preimage L _ ⟨a,rfl⟩
  have ht : L t=L b := global_preimage L _ ⟨b,rfl⟩
  have hu : L u=L a+L b := global_preimage L _ ⟨a+b,L.map_add a b⟩
  let k := r+t+u
  have hk : L k=0 := by
    change L (r+t+u)=0
    rw [map_add,map_add,hr,ht,hu]
    exact word_add_self (L a+L b)
  have hz : k=0 := by
    rcases first_one_or_zero (coordinates A) k with hz | ⟨q,hq,hkq,hbefore⟩
    · funext q
      exact hz q (mem_coordinates A q)
    · have hone : r q=1 ∨ t q=1 ∨ u q=1 := by
        rcases bit_cases (r q) with h | h
        · rcases bit_cases (t q) with j | j
          · rcases bit_cases (u q) with l | l
            · have hbad : (0 : Bit)=1 := by simpa only [k,Pi.add_apply,h,j,l,zero_add] using hkq
              exact False.elim (zero_ne_one hbad)
            · exact Or.inr (Or.inr l)
          · exact Or.inr (Or.inl j)
        · exact Or.inl h
      rcases hone with h | h | h
      · have he : L (r+k)=L a := by rw [map_add,hk,add_zero,hr]
        exact False.elim (global_minimal L (L a) ⟨a,rfl⟩ (r+k) he (hbefore r h))
      · have he : L (t+k)=L b := by rw [map_add,hk,add_zero,ht]
        exact False.elim (global_minimal L (L b) ⟨b,rfl⟩ (t+k) he (hbefore t h))
      · have he : L (u+k)=L a+L b := by rw [map_add,hk,add_zero,hu]
        exact False.elim (global_minimal L (L a+L b) ⟨a+b,L.map_add a b⟩
          (u+k) he (hbefore u h))
  change u=r+t
  calc
    u=0+u := (zero_add u).symm
    _=(r+t+u)+u := congrArg (fun z => z+u) hz.symm
    _=r+t := by rw [add_assoc,word_add_self,add_zero]

/-- The same result with arbitrary actual-image syndromes. -/
theorem global_add_image (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s t : Word Bit B) (hs : s∈LinearMap.range L) (ht : t∈LinearMap.range L) :
    G L (s+t)=G L s+G L t := by
  obtain ⟨a,rfl⟩ := hs
  obtain ⟨b,rfl⟩ := ht
  exact global_add_words L a b

/-- Binary scalar compatibility on the actual image. -/
theorem global_smul_image (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : Word Bit B) (hs : s∈LinearMap.range L) (c : Bit) :
    G L (c • s)=c • G L s := by
  rcases bit_cases c with rfl | rfl <;> simp [global_zero]

/-- The section is the ORIGINAL search restricted to its actual image. -/
def imageSection (L : Word Bit A →ₗ[Bit] Word Bit B) :
    LinearMap.range L →ₗ[Bit] Word Bit A where
  toFun s := G L s.val
  map_add' s t := global_add_image L s.val t.val s.property t.property
  map_smul' c s := global_smul_image L s.val s.property c

theorem imageSection_preimage (L : Word Bit A →ₗ[Bit] Word Bit B)
    (s : LinearMap.range L) : L (imageSection L s)=s.val :=
  global_preimage L s.val s.property

/-- Residual of every original word lies in the true kernel. -/
theorem residual_syndrome (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a : Word Bit A) : L (a+G L (L a))=0 := by
  rw [map_add,global_preimage L (L a) ⟨a,rfl⟩]
  exact word_add_self (L a)

/-- Full residual addition equality, not just an equality of logical classes. -/
theorem residual_add (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a b : Word Bit A) :
    (a+b)+G L (L (a+b))=(a+G L (L a))+(b+G L (L b)) := by
  rw [map_add,global_add_words]
  abel

/-- Exact failed-local branch of the unchanged generic lookup. -/
theorem lookup_eq_global_of_local_none (L : Word Bit A →ₗ[Bit] Word Bit B)
    (isLocal : Word Bit A → Bool) (s : Word Bit B)
    (h : search (fun e => isLocal e && decide (L e=s)) (allWords A)=none) :
    lookup (allWords A) L isLocal 0 s=G L s := by
  unfold lookup
  rw [h]
  rfl

/-- The finite incidence computation itself is a linear map. -/
def incidenceLinear {Q Z : Type} (F : Fintype Q) (inc : Q → Z → Bool) :
    Word Bit Q →ₗ[Bit] Word Bit Z where
  toFun := syndromeFromBits F inc
  map_add' a b := by
    funext z
    change (∑ q∈F.elems, if inc q z then a q+b q else 0)=_
    have he : ∀ q, (if inc q z then a q+b q else 0)=
        (if inc q z then a q else 0)+(if inc q z then b q else 0) := by
      intro q
      cases inc q z <;> simp
    simp_rw [he]
    exact Finset.sum_add_distrib
  map_smul' c a := by
    rcases bit_cases c with rfl | rfl
    · funext z
      simp [syndromeFromBits]
    · simp

/-- SAME executable finite syndrome and SAME explicit coordinate instances. -/
def executableLinear (S : OddScale) :
    Word Bit (ExecutableQ S) →ₗ[Bit] Word Bit (ExecutableZ S) where
  toFun := executableSyndrome S
  map_add' a b := by
    unfold executableSyndrome rawSyndrome
    exact (incidenceLinear _ _).map_add a b
  map_smul' c a := by
    unfold executableSyndrome rawSyndrome
    exact (incidenceLinear _ _).map_smul c a

theorem executableLinear_apply (S : OddScale) (a : Word Bit (ExecutableQ S)) :
    executableLinear S a=executableSyndrome S a := rfl

/-- Full agreement with the merged Tanner map through the ORIGINAL casts. -/
theorem executableLinear_actual (S : OddScale)
    (a : Word Bit (levelTwoPresentation S).Q) :
    executableLinear S (toExecutableError S a)=
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) a) :=
  executableSyndrome_eq S a

/-- Actual global representative on the executable physical C2 carrier. -/
def executableGlobal (S : OddScale) (s : Word Bit (ExecutableZ S)) :
    Word Bit (ExecutableQ S) := G (executableLinear S) s

theorem executableGlobal_zero (S : OddScale) : executableGlobal S 0=0 :=
  global_zero (executableLinear S)

theorem executableGlobal_preimage (S : OddScale) (a : Word Bit (ExecutableQ S)) :
    executableSyndrome S (executableGlobal S (executableSyndrome S a))=
      executableSyndrome S a := global_preimage (executableLinear S) _ ⟨a,rfl⟩

/-- All OddScale, all original physical words; no small-support hypothesis. -/
theorem executableGlobal_add (S : OddScale) (a b : Word Bit (ExecutableQ S)) :
    executableGlobal S (executableSyndrome S a+executableSyndrome S b)=
      executableGlobal S (executableSyndrome S a)+executableGlobal S (executableSyndrome S b) :=
  global_add_words (executableLinear S) a b

theorem executableGlobal_residual (S : OddScale) (a : Word Bit (ExecutableQ S)) :
    executableSyndrome S (a+executableGlobal S (executableSyndrome S a))=0 :=
  residual_syndrome (executableLinear S) a

/-- No local-first linearity: this identity requires the LITERAL local-none branch. -/
theorem executableDecode_of_local_none (S : OddScale) (s : Word Bit (ExecutableZ S))
    (h : search (fun e => executableLocal S e && decide (executableSyndrome S e=s))
      (allWords (ExecutableQ S))=none) :
    executableDecode S s=executableGlobal S s :=
  lookup_eq_global_of_local_none (executableLinear S) (executableLocal S) s h

/-- Original physical coordinate wrapper, preserving both cast directions. -/
def actualGlobal (S : OddScale) (s : Word Bit (levelTwoPresentation S).Z) :
    Word Bit (levelTwoPresentation S).Q :=
  toActualError S (executableGlobal S (toExecutableSyndrome S s))

theorem actualGlobal_zero (S : OddScale) : actualGlobal S 0=0 := by
  unfold actualGlobal
  rw [toExecutableSyndrome_zero,executableGlobal_zero,toActualError_zero]

/-- Complete addition identity for actual ORIGINAL Tanner words. -/
theorem actualGlobal_add (S : OddScale) (a b : Word Bit (levelTwoPresentation S).Q) :
    actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a+
      tannerCoboundary1 (levelTwoPresentation S) b)=
      actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a)+
      actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) b) := by
  have he := executableGlobal_add S (toExecutableError S a) (toExecutableError S b)
  simp only [executableSyndrome_eq] at he
  have ht : toExecutableSyndrome S
      (tannerCoboundary1 (levelTwoPresentation S) a+tannerCoboundary1 (levelTwoPresentation S) b)=
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) a)+
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) b) := rfl
  unfold actualGlobal
  rw [ht,he]
  rfl

/-- Full same-map preimage on actual ORIGINAL Tanner syndromes. -/
theorem actualGlobal_preimage (S : OddScale) (a : Word Bit (levelTwoPresentation S).Q) :
    tannerCoboundary1 (levelTwoPresentation S)
      (actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a))=
      tannerCoboundary1 (levelTwoPresentation S) a := by
  apply toExecutableSyndrome_injective S
  have hp : executableSyndrome S (executableGlobal S (toExecutableSyndrome S
      (tannerCoboundary1 (levelTwoPresentation S) a)))=
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) a) :=
    global_preimage (executableLinear S) _ ⟨toExecutableError S a,
      executableLinear_actual S a⟩
  have he : toExecutableError S (actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a))=
      executableGlobal S (toExecutableSyndrome S
        (tannerCoboundary1 (levelTwoPresentation S) a)) :=
    toExecutableError_toActualError S _
  exact (executableSyndrome_eq S (actualGlobal S
    (tannerCoboundary1 (levelTwoPresentation S) a))).symm.trans
      ((congrArg (executableSyndrome S) he).trans hp)

/-- Full original residual has zero syndrome; no boundary/filling claim follows. -/
theorem actualGlobal_residual (S : OddScale) (a : Word Bit (levelTwoPresentation S).Q) :
    tannerCoboundary1 (levelTwoPresentation S)
      (a+actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a))=0 := by
  rw [map_add,actualGlobal_preimage]
  exact word_add_self (tannerCoboundary1 (levelTwoPresentation S) a)

/-- Full old physical selector equality on its actual failed-local-search branch. -/
theorem decode_of_local_none (S : OddScale) (s : Word Bit (levelTwoPresentation S).Z)
    (h : search (fun e => executableLocal S e &&
      decide (executableSyndrome S e=toExecutableSyndrome S s))
      (allWords (ExecutableQ S))=none) : decode S s=actualGlobal S s := by
  unfold decode actualGlobal
  rw [executableDecode_of_local_none S _ h]

end QEC.Coding.BDL26GlobalLookupLinearity
