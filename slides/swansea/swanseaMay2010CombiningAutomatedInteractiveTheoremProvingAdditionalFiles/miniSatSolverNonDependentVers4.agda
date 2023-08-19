module miniSatSolverNonDependentVers4 where
 
{- variant of miniSatSolver
   so that the check uses no dependent types -}


{- The first part can be implemented in Haskell
  and doesn't make use of dependent types. -}

{- Basic sets -}

data ℕ : Set where
  zero : ℕ 
  _+1  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ   #-}
{-# BUILTIN SUC    _+1  #-}
{-# BUILTIN ZERO    zero #-}

max : ℕ → ℕ → ℕ 
max 0      n      = n 
max n      0      = n
max (n +1) (m +1) = (max n m) +1


data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  tt    #-}
{-# BUILTIN FALSE ff    #-}


_∧𝔹_ : 𝔹 → 𝔹 → 𝔹
tt ∧𝔹 b = b
ff ∧𝔹 _ = ff

_∨𝔹_ : 𝔹 → 𝔹 → 𝔹
tt ∨𝔹 _ = tt
ff ∨𝔹 b = b

¬𝔹 : 𝔹 → 𝔹
¬𝔹 tt = ff
¬𝔹 ff = tt



{- The data type of formulas -}

data For : Set where
  const  : 𝔹 →  For 
  x      : ℕ  →  For
  _∧for_ : For →  For →  For
  _∨for_ : For →  For →  For
  ¬for   : For  →  For 

{- check0 checks whether the formula is valid if all variables
are instantiated with tt -}

check0 : For →  𝔹
check0 (const b)  = b
check0 (x _)      = tt
check0 (φ ∧for ψ) = check0 φ ∧𝔹 check0 ψ
check0 (φ ∨for ψ) = check0 φ ∨𝔹 check0 ψ
check0 (¬for φ)   = ¬𝔹 (check0 φ)


instantiate- : For →  𝔹 →  For
instantiate-  (const b)     b' = const b
instantiate-  (x 0)         b  = const b
instantiate-  (x (m +1))    b  = x m
instantiate-  (φ ∧for ψ )   b  = (instantiate-  φ b ) ∧for (instantiate-  ψ b) 
instantiate-  (φ ∨for ψ )   b  = (instantiate-  φ b ) ∨for (instantiate-  ψ b) 
instantiate-  (¬for φ)      b  = ¬for (instantiate-  φ b ) 

{- check1 n checks whether a formula is valid if the variables with number
 >= n are instantiated with tt -}

check1 : For →  ℕ → 𝔹
check1 φ 0      = check0 φ
check1 φ (m +1) = check1 (instantiate- φ tt) m ∧𝔹 check1 (instantiate- φ ff) m 



maxVar : For → ℕ 
maxVar (const _)    = 0
maxVar (x n)        = n +1
maxVar (φ  ∧for ψ ) = max (maxVar φ) (maxVar ψ)
maxVar (φ ∨for ψ)   = max (maxVar φ) (maxVar ψ)
maxVar (¬for φ)     = maxVar φ





check : For → 𝔹
check φ = check1  φ (maxVar φ)


{- From here onwards we use dependent types.
   Up to the function check everything can be programmed
   in haskell, with check being replaced by a sat solver
   and then we can use builtins in a possible extension of Agda
   
   The rest is about proving that the above is correct -}


{- Further basic types -}

data ⊤ : Set where
  triv : ⊤ 

data ⊥ : Set where



data Vec (A : Set) : ℕ → Set where
  []   : Vec A 0
  _::_ : {n : ℕ} →  A →  Vec A n →  Vec A (n +1)

_≦_ : ℕ → ℕ → Set 
0    ≦ n    = ⊤ 
_ +1 ≦ 0    = ⊥ 
n +1 ≦ m +1 = n ≦ m


maxlem1 : (n m k : ℕ) → (max n m ≦ k) → n ≦ k
maxlem1 0      _       _       _ = triv
maxlem1 (_ +1) 0       _      p = p
maxlem1 (_ +1) (_ +1) 0       ()
maxlem1 (n +1) (m +1) (k +1) p = maxlem1 n m k p


maxlem2 : (n m k : ℕ) → (max n m ≦ k) → m ≦ k
maxlem2 _      0       _     _  = triv
maxlem2 0       (_ +1) _     p  = p
maxlem2 (_ +1) (_ +1) 0      () 
maxlem2 (n +1) (m +1) (k +1) p  = maxlem2 n m k p

{- leq operation on Nat -}

refl≦  : {n : ℕ} → n ≦ n
refl≦ {0}    = triv
refl≦ {n +1} = refl≦ {n}



-- allTt n 
-- is a Vector of length n consisting of tt
allTt : (n : ℕ) → Vec 𝔹 n
allTt 0      = []
allTt (n +1) = tt :: allTt n 




{- nthWithDefault a n v  
   returns the nth element of v if it exists
   if it doesn't exit it returns the default value a -}

nthWithDefault : {A : Set} →  (default : A) →  ℕ  → {n : ℕ} → Vec A n → A
nthWithDefault default _       []       = default
nthWithDefault default 0    (a :: _)    = a
nthWithDefault default (k +1) (_ :: v)  = nthWithDefault default k v


head : {A : Set} →  {n : ℕ} →  Vec A (n +1) →  A
head (a :: _) = a

tail : {A : Set} →  {n : ℕ} →  Vec A (n +1) →  Vec A n
tail (_ :: v) = v


-- truncateWithDefaultTt
-- truncates a list to a vector of length n
-- by cutting the list off after the nth element
-- and expanding it if necessary by adding tt
truncateWithDefaultTt : {m : ℕ} → Vec 𝔹 m → (n : ℕ) → Vec 𝔹 n
truncateWithDefaultTt  []          n       = allTt n
truncateWithDefaultTt  (_ :: _)    0       = []
truncateWithDefaultTt  (b :: bvec) (n +1)  = b :: truncateWithDefaultTt bvec n



{- Logic -}

Atom : 𝔹 → Set
Atom tt = ⊤ 
Atom ff = ⊥ 


data _∧_ (A B :  Set) : Set where
  and : A →  B →  A ∧ B

data _∨_ (A B :  Set) : Set where
  inl : A →  A ∨ B
  inr : B →  A ∨ B

¬ : Set → Set
¬ A = A → ⊥ 


_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)





{- Lifting of check0, check1 check from 𝔹 to Set using Atom -}

Check0 : For →  Set
Check0 φ = Atom (check0 φ)



Check1 : For →  (n : ℕ) → Set
Check1 φ n = Atom (check1 φ n)


Check : For →  Set
Check φ = Atom (check φ)



{- Conversion of elements of For into formulas
  
  [[ φ ]]
    gives formulas of the form
    ( (Atom b ∧ Atom b') ∨ (¬ (Atom b))) ∨ (¬ (Atom b') )

  [[ φ ]]' 
    gives formulas of the form
    Atom (((b ∧𝔹 b') ∨𝔹 ¬𝔹 b) ∨𝔹 ¬𝔹 b')


  [[ φ ]]b gives the boolean value used in
   [[ φ ]]' n 

  all variables with number >= n are replaced by the default
  value tt
-}
  
[[_]] : For →  {n : ℕ} → Vec 𝔹 n →  Set
[[ const b  ]] _    = Atom b
[[ x k      ]] bvec = Atom (nthWithDefault tt k bvec)
[[ φ ∧for ψ ]] bvec = [[ φ ]] bvec ∧ [[ ψ ]] bvec
[[ φ ∨for ψ ]] bvec = [[ φ ]] bvec ∨ [[ ψ ]] bvec
[[ ¬for φ   ]] bvec = ¬ ([[ φ ]] bvec)

[[_]]b  : For →  {n : ℕ} →  Vec 𝔹 n →  𝔹
[[ const b   ]]b _    = b
[[ x k       ]]b bvec = nthWithDefault tt  k bvec
[[ φ  ∧for ψ ]]b bvec = [[ φ ]]b bvec ∧𝔹 [[ ψ ]]b bvec
[[ φ ∨for ψ  ]]b bvec = [[ φ ]]b bvec ∨𝔹 [[ ψ ]]b bvec
[[ ¬for φ    ]]b bvec = ¬𝔹 ([[ φ ]]b bvec)

[[_]]' : For →  {n : ℕ} →  Vec 𝔹 n →  Set
[[ φ ]]' bvec = Atom ([[ φ ]]b bvec)



{- Lemmas about ∧ ∨ ¬ -}

lemma∧proj1 : (A B : Set) →  A ∧ B  → A
lemma∧proj1 A B (and a _) = a

lemma∧proj2 : (A B : Set) →  A ∧ B  → B
lemma∧proj2 A B (and _ b) = b


lemma∧1 : (b b' : 𝔹) →   Atom (b ∧𝔹 b') → Atom b ∧ Atom b' 
lemma∧1 tt _ p = and triv p
lemma∧1 ff _ () 

lemma∧2 : (b b' : 𝔹) →   Atom b ∧ Atom b' → Atom (b ∧𝔹 b')
lemma∧2 tt _ (and _  q) = q
lemma∧2 ff _ (and () _ )


lemma∧→ : (A B C D : Set) →  (A →  C) →  (B →  D) →  (A ∧ B) →  C ∧ D
lemma∧→ A B C D f g (and a b) = and (f a) (g b)


lemma∨1 : (b b' : 𝔹) →   Atom (b ∨𝔹 b') → Atom b ∨  Atom b' 
lemma∨1 tt _ _ = inl triv
lemma∨1 ff _ p = inr p

lemma∨2 : (b b' : 𝔹) →   Atom b ∨  Atom b'  → Atom (b ∨𝔹 b')  
lemma∨2 tt _ _        = triv
lemma∨2 ff _ (inl ())
lemma∨2 ff _ (inr p)  = p

lemma∨→ : (A B C D : Set) →  (A →  C) →  (B →  D) →  (A ∨ B) →  C ∨ D
lemma∨→ A B C D f g (inl a) = inl (f a)
lemma∨→ A B C D f g (inr b) = inr (g b)

lemma¬1 : (b : 𝔹) →   Atom (¬𝔹 b) → ¬ (Atom b)
lemma¬1 tt p _ = p
lemma¬1 ff _ p = p

lemma¬2 : (b : 𝔹) →   ¬ (Atom b) → Atom (¬𝔹 b)  
lemma¬2 tt p  = p triv
lemma¬2 ff _  = triv

lemma¬→ : (A B : Set) →  (B →  A) →  ¬ A → ¬ B
lemma¬→ A B f g b = g (f b)


{- Proof of the correctness -}

{- Step 1 we prove 
   Check0 φ  ↔ [[ φ ]] [] 
   this shows that correctness of check1 φ 0 ,
  i.e. gives in the inductive proof of correctnessCheck1
  the base case

-}


mutual
  lemma1a : (φ : For) →  Check0 φ →  [[ φ ]] []
  lemma1a (const _)  p = p
  lemma1a (x k)      p = p
  lemma1a (φ ∧for ψ) p = lemma∧→ 
                           (Check0 φ) 
                           (Check0 ψ ) 
                           ([[ φ ]] []) 
                           ([[ ψ ]] []) 
                           (lemma1a φ) 
                           (lemma1a ψ) 
                           (lemma∧1 ((check0 φ)) ((check0 ψ)) p)
  lemma1a (φ ∨for ψ) p = lemma∨→ 
                           (Check0 φ) 
                           (Check0 ψ) 
                           ([[ φ ]] [])
                           ([[ ψ ]] []) 
                           (lemma1a φ) 
                           (lemma1a ψ)
                           (lemma∨1 (check0 φ) (check0 ψ) p)
  lemma1a (¬for φ )  p = lemma¬→ 
                          (Check0 φ) 
                          ([[ φ ]] []) 
                          (lemma1b φ) 
                          (lemma¬1 ((check0 φ)) p)

  lemma1b : (φ : For) →  [[ φ ]] [] → Check0 φ
  lemma1b (const _)  p          = p
  lemma1b (x _)      p          = p
  lemma1b (φ ∧for ψ) (and p q)  = lemma∧2 (check0 φ) (check0 ψ) 
                                          (and (lemma1b φ p) (lemma1b ψ q))
  lemma1b (φ ∨for ψ) (inl p)    = lemma∨2 (check0 φ) (check0 ψ) 
                                          (inl (lemma1b φ p))
  lemma1b (φ ∨for ψ) (inr p)    = lemma∨2 (check0 φ) (check0 ψ) 
                                          (inr (lemma1b ψ p))
  lemma1b (¬for φ)   p          = lemma¬2 (check0 φ) 
                                          (lemma¬→ ([[ φ ]] []) 
                                                   (Check0 φ) 
                                                   (lemma1a φ) p)


{- Step 2 we prove 
   [[ φ ]] bvec  
   ↔ 
   [[ instantiate- φ (head bvec)]]  (tail bvec)

 This implies that 
   forall bvec →  [[ φ ]] bvec  
   ↔ 
   forall bvec →  [[ instantiate- φ tt ]] bvec
             ∧ 
             [[ instantiate- φ ff ]] bvec

  Since check reduces check1 φ (n +1) 
  to check1 (instantiate- φ tt) n bvec 
     ∧bool
    check1 (instantiate- φ ff) n bvec 
  this allows to show the correctness of check1 in the 
  induction step of correctnessCheck1

 
-}
mutual
  lemma2a : (φ : For) 
            →  {n : ℕ} 
            → (bvec : Vec 𝔹 (n +1)) 
            →  [[ φ ]] bvec 
            →  [[ instantiate- φ (head bvec) ]] (tail bvec)
  lemma2a (const _)     _           p = p
  lemma2a (x 0)         (_ :: _)    p = p
  lemma2a (x (k +1))    (_ :: _)    p = p
  lemma2a (φ ∧for ψ )   bvec        p = lemma∧→ 
                                         ([[ φ ]] bvec) 
                                         ([[ ψ ]] bvec) 
                                         ([[ instantiate- φ (head bvec) ]] (tail bvec)) 
                                         ([[ instantiate- ψ (head bvec) ]] (tail bvec)) 
                                         (lemma2a φ bvec) 
                                         (lemma2a ψ bvec) 
                                         p
  lemma2a (φ ∨for ψ ) bvec p = lemma∨→ 
                                   ([[ φ ]]  bvec) 
                                   ([[ ψ ]] bvec) 
                                   ([[ instantiate- φ (head bvec) ]] (tail bvec)) 
                                   ([[ instantiate- ψ (head bvec) ]] (tail bvec)) 
                                   (lemma2a φ bvec) 
                                   (lemma2a ψ bvec) 
                                   p
  lemma2a (¬for φ) bvec p = lemma¬→ 
                                 ([[ φ ]] bvec) 
                                 ([[ instantiate- φ (head bvec) ]] (tail bvec)) 
                                 (lemma2b φ bvec) 
                                 p


  lemma2b : (φ : For) 
            →  {n : ℕ} 
            → (bvec : Vec 𝔹 (n +1)) 
            →   [[ instantiate- φ (head bvec) ]] (tail bvec)
            →  [[ φ ]]  bvec 
  lemma2b (const _)     _           p = p
  lemma2b (x 0)         (_ :: _)    p = p
  lemma2b (x (_ +1))    (_ :: _)    p = p
  lemma2b (φ ∧for ψ)    bvec        p = lemma∧→ 
                                        ([[ instantiate- φ (head bvec) ]] 
                                         (tail bvec)) 
                                        ([[ instantiate- ψ (head bvec) ]] 
                                         (tail bvec)) 
                                        ([[ φ ]] bvec) 
                                        ([[ ψ ]] bvec) 
                                        (lemma2b φ bvec) 
                                        (lemma2b ψ bvec) 
                                        p
  lemma2b (φ ∨for ψ) bvec p = lemma∨→ 
                                   ([[ instantiate- φ (head bvec) ]] (tail bvec)) 
                                   ([[ instantiate- ψ (head bvec) ]] (tail bvec)) 
                                   (([[ φ ]] bvec)) 
                                   (([[ ψ ]] bvec)) 
                                   (lemma2b φ bvec) 
                                   (lemma2b ψ bvec) 
                                   p
  lemma2b (¬for φ) bvec p = lemma¬→ 
                                  ([[ instantiate- φ (head bvec) ]] (tail bvec)) 
                                  (([[ φ ]] bvec)) 
                                  (lemma2a φ bvec) 
                                  p



{-   lemma3 shows that [[ φ ]]  bvec and [[ φ ]]' bvec
    are equivalent.
    It is useful since formulas to be proved occur in both forms.

    This lemma is not needed for correctnessCheck1
    but for transfering the result of correctnessCheck1 to [[ φ ]]'
-}




mutual
  lemma3a : (φ : For) 
            → {n : ℕ} 
            → (bvec : Vec 𝔹 n) 
            → [[ φ ]]  bvec 
            → [[ φ ]]' bvec
  lemma3a (const _)  _    p         = p
  lemma3a (x _)      _    p         = p
  lemma3a (φ ∧for ψ) bvec (and p q) = lemma∧2 
                                          ([[ φ ]]b bvec) 
                                          ([[ ψ ]]b bvec) 
                                          (and (lemma3a φ bvec p) (lemma3a ψ bvec q)) 
  lemma3a (φ ∨for ψ) bvec (inl p)   = lemma∨2 
                                         ([[ φ ]]b bvec) 
                                          ([[ ψ ]]b bvec) 
                                          (inl (lemma3a φ bvec p))
  lemma3a (φ ∨for ψ) bvec (inr q)   = lemma∨2 
                                         ([[ φ ]]b bvec) 
                                         ([[ ψ ]]b bvec)
                                         (inr (lemma3a ψ bvec q))
  lemma3a (¬for φ ) bvec p          = lemma¬2 
                                         ([[ φ ]]b bvec) 
                                         (lemma¬→ ([[ φ ]]  bvec) 
                                                  ([[ φ ]]' bvec) 
                                                  (lemma3b φ bvec) p)

  lemma3b : (φ : For) 
            → {n : ℕ} 
            → (bvec : Vec 𝔹 n) 
            → [[ φ ]]' bvec 
            → [[ φ ]]  bvec
  lemma3b (const _)   _    p = p
  lemma3b (x _)       _    p = p
  lemma3b (φ  ∧for ψ) bvec p = and 
                                  (lemma3b φ bvec 
                                     (lemma∧proj1 
                                       ([[ φ ]]' bvec) 
                                       ([[ ψ ]]' bvec) 
                                       (lemma∧1 
                                         ([[ φ ]]b bvec) 
                                         ([[ ψ ]]b bvec) 
                                        p))) 
                                  (lemma3b ψ bvec
                                     (lemma∧proj2 
                                        ([[ φ ]]' bvec) 
                                        ([[ ψ ]]' bvec)
                                      (lemma∧1 
                                        ([[ φ ]]b bvec) 
                                        ([[ ψ ]]b bvec) 
                                       p))) 
  lemma3b (φ  ∨for ψ) bvec p = lemma∨→ 
                                   ([[ φ ]]' bvec) 
                                   ([[ ψ ]]' bvec) 
                                   ([[ φ ]]  bvec) 
                                   ([[ ψ ]] bvec) 
                                   (lemma3b φ bvec) 
                                   (lemma3b ψ bvec) 
                                   (lemma∨1 
                                      ([[ φ ]]b bvec) 
                                      ([[ ψ ]]b bvec) 
                                      p)
  lemma3b (¬for φ) bvec p = lemma¬→ 
                                ([[ φ ]]' bvec) 
                                ([[ φ ]]  bvec) 
                                (lemma3a φ bvec) 
                                (lemma¬1 ([[ φ ]]b bvec) p) 



{- The following are auxiliary lemmata used in lemma4a and lemma4b -}
lemmaNthWithDefault1 : {k : ℕ} 
                       → (bvec : Vec 𝔹 k) 
                       → (n m : ℕ) 
                       → ((m +1) ≦ n) 
                       → Atom (nthWithDefault tt m (truncateWithDefaultTt bvec n))                  
                       → Atom (nthWithDefault tt m bvec)
lemmaNthWithDefault1 []          _      _      _  _ = triv
lemmaNthWithDefault1 (_ :: _)    0      0      () _
lemmaNthWithDefault1 (_ :: _)    (_ +1) 0      _  p = p
lemmaNthWithDefault1 (_ :: _)    0      (_ +1) () _
lemmaNthWithDefault1 (_ :: bvec) (n +1) (m +1) mn p = lemmaNthWithDefault1 
                                                        bvec n m mn p

lemmaNthWithDefault2aux : (n m : ℕ) → Atom (nthWithDefault tt m (allTt n))
lemmaNthWithDefault2aux 0      _      = triv
lemmaNthWithDefault2aux (_ +1) 0      = triv
lemmaNthWithDefault2aux (n +1) (m +1) = lemmaNthWithDefault2aux n m

lemmaNthWithDefault2 : {k : ℕ} 
                       → (bvec : Vec 𝔹 k) 
                       → (n m : ℕ) 
                       → ((m +1) ≦ n) 
                       → Atom (nthWithDefault tt m bvec)
                       → Atom (nthWithDefault tt m (truncateWithDefaultTt bvec n))                  
lemmaNthWithDefault2 []          n      m      _  _ = lemmaNthWithDefault2aux 
                                                        n m
lemmaNthWithDefault2 (_ :: _)    0      _      _  _ = triv
lemmaNthWithDefault2 (_ :: _)    (_ +1) 0      _  p = p
lemmaNthWithDefault2 (_ :: bvec) (n +1) (m +1) mn p = lemmaNthWithDefault2 
                                                        bvec n m mn p


{- 
We show that the truth of [[ φ ]] depends only on vectors up to 
the length of the number of variables of φ 

-}




mutual
  lemma4a : (φ : For) 
            → (n : ℕ) 
            → ((maxVar φ) ≦ n) 
            → {m : ℕ}
            → (bvec : Vec 𝔹 m) 
            → [[ φ ]] bvec
            → [[ φ ]] (truncateWithDefaultTt bvec n)
  lemma4a (const _)  _ _ _    q          = q
  lemma4a (x m)      n p bvec q          = lemmaNthWithDefault2 bvec n m p q
  lemma4a (φ ∧for ψ) n p bvec (and q q') = and 
                                            (lemma4a φ n 
                                              (maxlem1 
                                                 (maxVar φ) 
                                                 (maxVar ψ) 
                                                 n p) 
                                               bvec q) 
                                            (lemma4a ψ n 
                                              (maxlem2 
                                                (maxVar φ) 
                                                (maxVar ψ) 
                                                n p)
                                               bvec q')
  lemma4a (φ ∨for ψ) n p bvec (inl q)     = inl
                                             (lemma4a φ n 
                                               (maxlem1 (maxVar φ) 
                                                        (maxVar ψ) n p)
                                               bvec q)
  lemma4a (φ ∨for ψ) n p bvec (inr q)      = inr
                                              (lemma4a ψ n 
                                                (maxlem2 (maxVar φ) 
                                                    (maxVar ψ) n p)
                                                bvec q)
  lemma4a (¬for φ) n p bvec q = λ p' → q (lemma4b φ n p bvec p')

  lemma4b : (φ : For) 
            → (n : ℕ) 
            → ((maxVar φ) ≦ n) 
            → {m : ℕ}
            → (bvec : Vec 𝔹 m) 
            → [[ φ ]] (truncateWithDefaultTt bvec n)
            → [[ φ ]] bvec
  lemma4b (const _)  _ _ _    q          = q
  lemma4b (x k)      n p bvec q          = lemmaNthWithDefault1 bvec n k p q
  lemma4b (φ ∧for ψ) n p bvec (and q q') = and 
                                             (lemma4b φ n 
                                               (maxlem1 (maxVar φ) 
                                                        (maxVar ψ) n p)
                                                bvec q) 
                                             (lemma4b ψ n 
                                               (maxlem2 (maxVar φ) 
                                                        (maxVar ψ) n p)
                                                bvec q')
  lemma4b (φ ∨for ψ) n p bvec (inl q)    = inl
                                           (lemma4b φ n 
                                             (maxlem1 (maxVar φ) 
                                                      (maxVar ψ) n p)
                                           bvec q)
  lemma4b (φ ∨for ψ) n p bvec (inr q)    = inr
                                           (lemma4b ψ n 
                                             (maxlem2 (maxVar φ) 
                                                      (maxVar ψ) n p)
                                            bvec q)
  lemma4b (¬for φ )  n p bvec q          = λ p' → q (lemma4a φ n p bvec p')




{- Now we show 
   Check1 φ n 
   ↔ 
  (bvec : Vec 𝔹 n) →  [[ φ ]]  bvec 

 i.e. check1 is correct
-}




mutual
 correctnessCheck1a : (φ : For) 
                      →  {n : ℕ} 
                       → (Check1 φ n )   
                       →  (bvec : Vec 𝔹 n) 
                       →  [[ φ ]]  bvec
 correctnessCheck1a φ         p []            = lemma1a φ p
 correctnessCheck1a φ {n +1}  p (tt :: bvec)  = lemma2b φ (tt :: bvec)
                                                  (correctnessCheck1a 
                                                   (instantiate- φ tt) 
                                                   (lemma∧proj1 
                                                    (Check1 (instantiate- φ tt) n)
                                                    (Check1 (instantiate- φ ff) n)
                                                    (lemma∧1 
                                                     (check1 (instantiate- φ tt) n)
                                                      (check1 (instantiate- φ ff) n) 
                                                      p))
                                                   bvec)
                                               
 correctnessCheck1a φ {n +1} p (ff :: bvec) = lemma2b φ (ff :: bvec)
                                                (correctnessCheck1a 
                                                 (instantiate- φ ff) 
                                                 (lemma∧proj2 
                                                  (Check1 (instantiate- φ tt) n)
                                                  (Check1 (instantiate- φ ff) n)
                                                  (lemma∧1 
                                                   (check1 (instantiate- φ tt) n)
                                                   (check1 (instantiate- φ ff) n) 
                                                   p))
                                                bvec)
                                               


 correctnessCheck1b : (φ : For) 
                      →  {n : ℕ} 
                      →  ((bvec : Vec 𝔹 n) →  [[ φ ]]  bvec) 
                      → Check1 φ n   
 correctnessCheck1b φ {0}  p = lemma1b φ (p [])
 correctnessCheck1b φ {n +1} p = lemma∧2 
                                  (check1 (instantiate- φ tt) n) 
                                  (check1 (instantiate- φ ff) n) 
                                  (and 
                                   (correctnessCheck1b 
                                     (instantiate- φ tt) 
                                     (λ bvec → lemma2a φ (tt :: bvec) 
                                                         (p (tt :: bvec)))) 
                                   (correctnessCheck1b 
                                     (instantiate- φ ff) 
                                     (λ bvec → lemma2a φ (ff :: bvec) 
                                                         (p (ff :: bvec)))))

correctnessCheck1 : (φ : For) 
                    →  (n : ℕ) 
                    →  (Check1 φ n)  ↔ ((b : Vec 𝔹 n) →  [[ φ ]]  b)
correctnessCheck1 φ n = and (correctnessCheck1a φ) (correctnessCheck1b φ)


correctnessCheck : (φ : For) 
                   →  Check φ   
                   →  {n : ℕ} 
                   → (bvec : Vec 𝔹 n) 
                   →  [[ φ ]]  bvec
correctnessCheck φ p {n} bvec = lemma4b 
                                 φ 
                                 (maxVar φ) 
                                 refl≦ 
                                 bvec 
                                 (correctnessCheck1a φ 
                                  {maxVar φ} p 
                                  (truncateWithDefaultTt bvec 
                                   (maxVar φ)))


correctnessCheck' : (φ : For) 
                    →  Check φ   
                    →  {n : ℕ} 
                    → (bvec : Vec 𝔹 n) 
                    →  [[ φ ]]'  bvec
correctnessCheck' φ p bvec = lemma3a φ bvec (correctnessCheck φ p bvec)




{- Example -}


x₀ : For
x₀ = x 0

x₁ : For
x₁ = x 1

example1 : For 
example1 =  ((x₀  ∧for x₁)   ∨for (¬for x₀)) ∨for (¬for x₁)

for1 : 𝔹 → 𝔹 → Set
for1 b b'  = ((Atom b ∧ Atom b') ∨ ¬ (Atom b)) ∨ ¬ (Atom b')
            {- equal to [[ example1 ]] (b :: (b' :: [])) -}

for1' : 𝔹 → 𝔹 → Set
for1' b b'  = Atom (((b ∧𝔹 b') ∨𝔹 ¬𝔹 b) ∨𝔹 ¬𝔹 b')
              {- equal to [[ example1 ]]' (b :: (b' :: []))-}

postulate b : 𝔹
postulate b' : 𝔹

for1inst : Set
for1inst = for1 b b' 
{- equal to ((Atom b ∧ Atom b') ∨ (¬ (Atom b)) ∨ (¬ (Atom b')) -}

for1'inst : Set
for1'inst = for1' b b' 
{- equal to Atom (((b ∧𝔹 b') ∨𝔹 ¬𝔹 b) ∨𝔹 ¬𝔹 b') -}


proof : (b b' : 𝔹) →  ( (Atom b ∧ Atom b') ∨ (¬ (Atom b))) ∨ (¬ (Atom b') )
proof b b' = correctnessCheck example1 triv (b :: (b' :: []))  

{- as well
   proof : (b b' : 𝔹 → for1 b b' -}


proof' : (b b' : 𝔹) →  Atom (((b ∧𝔹 b') ∨𝔹 ¬𝔹 b) ∨𝔹 ¬𝔹 b')
proof' b b' = correctnessCheck' example1 triv (b :: (b' :: []))  


