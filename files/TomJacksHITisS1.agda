{-# OPTIONS --cubical #-}

module BakerCircle where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level
    A : Type ℓ
    x : A

Ω Ω² : (A : Type ℓ) → A → Type ℓ
Ω A x = Path A x x
Ω² A x = Ω (Ω A x) refl

csq : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → Ω² A y
  → PathP (λ i → p i ≡ q i) p q
csq p q r i j =
  hcomp (λ k → λ { (i = i0) → p (~ k ∨ j)
                 ; (i = i1) → q (k ∧ j)
                 ; (j = i0) → p (~ k ∨ i)
                 ; (j = i1) → q (k ∧ i)
                 })
        (r i j)

csqPath : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → Ω² A y ≡ PathP (λ i → p i ≡ q i) p q
csqPath {A = A} p q k =
  PathP (λ i → PathP (λ j → A)
                     (p (~ k ∨ i))
                     (q (k ∧ i)))
        (λ j → p (~ k ∨ j))
        (λ j → q (k ∧ j))

csqFill : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → (r : Ω² A y) → PathP (λ t → csqPath p q t) r (csq p q r)
csqFill {A = A} p q r t i j =
  hfill (λ k → λ { (i = i0) → p (~ k ∨ j)
                 ; (i = i1) → q (k ∧ j)
                 ; (j = i0) → p (~ k ∨ i)
                 ; (j = i1) → q (k ∧ i)
                 })
        (inS (r i j))
        t

data X : Type where
  base : X
  loops : (x : X) → x ≡ x
  triv : PathP (λ t → csqPath (loops base) (loops base) t)
               refl
               (λ i j → loops (loops base i) j)

φ : X → S¹
φ base = base
φ (loops x i) = rotLoop (φ x) i
φ (triv t i j) = csqFill loop loop refl t i j

ψ : S¹ → X
ψ base = base
ψ (loop i) = loops base i

φψ : (x : S¹) → φ (ψ x) ≡ x
φψ base = refl
φψ (loop i) = refl

ψ-rotLoop : (x : S¹) → PathP (λ i → loops (ψ x) i ≡ ψ (rotLoop x i)) refl refl
ψ-rotLoop base j = refl
ψ-rotLoop (loop i) j k =
  hcomp (λ l → λ { (i = i0) → loops base (~ l ∨ j)
                 ; (i = i1) → loops base (l ∧ j)
                 ; (j = i0) → loops base (~ l ∨ i)
                 ; (j = i1) → loops base (l ∧ i)
                 ; (k = i0) → triv l i j
                 })
        base

ψφ : (x : X) → ψ (φ x) ≡ x
ψφ base = refl
ψφ (loops x i) = thing (ψφ x) i
  where
  thing : (h : ψ (φ x) ≡ x) → PathP (λ i → ψ (rotLoop (φ x) i) ≡ loops x i) h h
  thing h i j =
    hcomp (λ k → λ { (i = i0) → h j
                   ; (i = i1) → h j
                   ; (j = i0) → ψ-rotLoop (φ x) i k
                   ; (j = i1) → loops x i
                   })
          (loops (h j) i)
ψφ (triv t i j) = lol4 t i j
  where
  lol1 : PathP (λ t → PathP (λ i → PathP (λ j → base ≡ base)
                                         (λ k → base)
                                         (λ k → base))
                            (λ j k → base)
                            (λ j k → base))
               (λ i j k → base)
               (λ i j k → hcomp (λ l → λ { (i = i0) → base
                                         ; (i = i1) → base
                                         ; (j = i0) → base
                                         ; (j = i1) → base
                                         ; (k = i0) → base
                                         ; (k = i1) → base
                                         })
                                base)
  lol1 t i j k =
    hcomp (λ l → λ { (i = i0) → base
                   ; (i = i1) → base
                   ; (j = i0) → base
                   ; (j = i1) → base
                   ; (k = i0) → base
                   ; (k = i1) → base
                   ; (t = i0) → base
                   })
          base

  lol2 : PathP (λ t → PathP (λ i → PathP (λ j → triv t i j ≡ triv t i j)
                                         (λ k → loops base (~ t ∨ i))
                                         (λ k → loops base (t ∧ i)))
                            (λ j k → loops base (~ t ∨ j))
                            (λ j k → loops base (t ∧ j)))
               (λ i j k → base)
               (λ i j k → hcomp (λ l → λ { (i = i0) → loops base j
                                         ; (i = i1) → loops base j
                                         ; (j = i0) → loops base i
                                         ; (j = i1) → loops base i
                                         ; (k = i0) → loops (loops base i) j
                                         ; (k = i1) → loops (loops base i) j
                                         })
                                (loops (loops base i) j))
  lol2 t i j k =
    hcomp (λ z → λ { (t = i0) → base
                   ; (t = i1) → hcomp (λ l → λ { (i = i0) → loops base (~ z ∨ j)
                                               ; (i = i1) → loops base (z ∧ j)
                                               ; (j = i0) → loops base (~ z ∨ i)
                                               ; (j = i1) → loops base (z ∧ i)
                                               ; (k = i0) → triv z i j
                                               ; (k = i1) → triv z i j
                                               })
                                      (triv z i j)
                   ; (i = i0) → loops base (~ t ∨ ~ z ∨ j)
                   ; (i = i1) → loops base (t ∧ z ∧ j)
                   ; (j = i0) → loops base (~ t ∨ ~ z ∨ i)
                   ; (j = i1) → loops base (t ∧ z ∧ i)
                   ; (k = i0) → triv (t ∧ z) i j
                   ; (k = i1) → triv (t ∧ z) i j
                   })
          (lol1 t i j k)

  lol3 : PathP (λ t → PathP (λ i → PathP (λ j → hcomp (λ k → λ { (i = i0) → loops base (~ k ∨ ~ t ∨ j)
                                                               ; (i = i1) → loops base (k ∧ t ∧ j)
                                                               ; (j = i0) → loops base (~ k ∨ ~ t ∨ i)
                                                               ; (j = i1) → loops base (k ∧ t ∧ i)
                                                               ; (t = i0) → base
                                                               })
                                                      base
                                                ≡ triv t i j)
                                         (λ k → loops base (~ t ∨ i))
                                         (λ k → loops base (t ∧ i)))
                            (λ j k → loops base (~ t ∨ j))
                            (λ j k → loops base (t ∧ j)))
               (λ i j k → base)
               (λ i j k → hcomp (λ l → λ { (i = i0) → loops base j
                                         ; (i = i1) → loops base j
                                         ; (j = i0) → loops base i
                                         ; (j = i1) → loops base i
                                         ; (k = i0) → hcomp (λ m → λ { (i = i0) → loops base (~ m ∨ j)
                                                                     ; (i = i1) → loops base (m ∧ j)
                                                                     ; (j = i0) → loops base (~ m ∨ i)
                                                                     ; (j = i1) → loops base (m ∧ i)
                                                                     ; (l = i0) → triv m i j
                                                                     })
                                                            base
                                         ; (k = i1) → loops (loops base i) j
                                         })
                                (loops (loops base i) j))
  lol3 t i j k =
    hcomp (λ z → λ { (t = i0) → base
                   ; (t = i1) → hcomp (λ l → λ { (i = i0) → loops base j
                                             ; (i = i1) → loops base j
                                             ; (j = i0) → loops base i
                                             ; (j = i1) → loops base i
                                             ; (k = i0) → hcomp (λ m → λ { (i = i0) → loops base (~ m ∨ j)
                                                                         ; (i = i1) → loops base (m ∧ j)
                                                                         ; (j = i0) → loops base (~ m ∨ i)
                                                                         ; (j = i1) → loops base (m ∧ i)
                                                                         ; (l = i0) → triv m i j
                                                                         ; (z = i0) → triv m i j -- ???
                                                                         })
                                                                base
                                             ; (k = i1) → loops (loops base i) j
                                             })
                                    (loops (loops base i) j)
                   ; (i = i0) → loops base (~ t ∨ j)
                   ; (i = i1) → loops base (t ∧ j)
                   ; (j = i0) → loops base (~ t ∨ i)
                   ; (j = i1) → loops base (t ∧ i)
                   ; (k = i0) → hcomp (λ k → λ { (i = i0) → loops base (~ k ∨ ~ t ∨ j)
                                               ; (i = i1) → loops base (k ∧ t ∧ j)
                                               ; (j = i0) → loops base (~ k ∨ ~ t ∨ i)
                                               ; (j = i1) → loops base (k ∧ t ∧ i)
                                               ; (t = i0) → base
                                               ; (z = i0) → triv (k ∧ t) i j
                                               })
                                      base
                   ; (k = i1) → triv t i j
                   })
          (lol2 t i j k)

  lol4 : PathP (λ t → PathP (λ i → PathP (λ j → hcomp (λ k → λ { (i = i0) → loops base (~ k ∨ ~ t ∨ j)
                                                               ; (i = i1) → loops base (k ∧ t ∧ j)
                                                               ; (j = i0) → loops base (~ k ∨ ~ t ∨ i)
                                                               ; (j = i1) → loops base (k ∧ t ∧ i)
                                                               ; (t = i0) → base
                                                               })
                                                      base
                                                ≡ triv t i j)
                                         (λ k → hcomp (λ _ → λ { (t = i1) (i = i0) → base
                                                               ; (t = i0) → base
                                                               ; (i = i1) → base
                                                               ; (k = i0) → loops base (~ t ∨ i)
                                                               ; (k = i1) → loops base (~ t ∨ i)
                                                               })
                                                      (loops base (~ t ∨ i)))
                                         (λ k → hcomp (λ _ → λ { (t = i0) → base
                                                               ; (i = i0) → base
                                                               ; (t = i1) (i = i1) → base
                                                               ; (k = i0) → loops base (t ∧ i)
                                                               ; (k = i1) → loops base (t ∧ i)
                                                               })
                                                      (loops base (t ∧ i))))
                            (λ j k → hcomp (λ _ → λ { (t = i1) (j = i0) → base
                                                    ; (t = i0) → base
                                                    ; (j = i1) → base
                                                    ; (k = i0) → loops base (~ t ∨ j)
                                                    ; (k = i1) → loops base (~ t ∨ j)
                                                    })
                                           (loops base (~ t ∨ j)))
                            (λ j k → hcomp (λ _ → λ { (t = i0) → base
                                                    ; (j = i0) → base
                                                    ; (t = i1) (j = i1) → base
                                                    ; (k = i0) → loops base (t ∧ j)
                                                    ; (k = i1) → loops base (t ∧ j)
                                                    })
                                           (loops base (t ∧ j))))
               (λ i j k → base)
               (λ i j k → hcomp (λ l → λ { (j = i0) → hcomp (λ _ → λ { (i = i0) → base
                                                                     ; (i = i1) → base
                                                                     ; (k = i0) → loops base i
                                                                     ; (k = i1) → loops base i
                                                                     })
                                                            (loops base i)
                                         ; (j = i1) → hcomp (λ _ → λ { (i = i0) → base
                                                                     ; (i = i1) → base
                                                                     ; (k = i0) → loops base i
                                                                     ; (k = i1) → loops base i
                                                                     })
                                                            (loops base i)
                                         ; (k = i0) → hcomp (λ m → λ { (i = i0) → loops base (~ m ∨ j)
                                                                     ; (i = i1) → loops base (m ∧ j)
                                                                     ; (j = i0) → loops base (~ m ∨ i)
                                                                     ; (j = i1) → loops base (m ∧ i)
                                                                     ; (l = i0) → triv m i j
                                                                     })
                                                            base
                                         ; (k = i1) → loops (loops base i) j
                                         })
                                (loops (hcomp (λ _ → λ { (i = i0) → base
                                                       ; (i = i1) → base
                                                       ; (k = i0) → loops base i
                                                       ; (k = i1) → loops base i
                                                       })
                                              (loops base i))
                                       j))
  lol4 t i j k =
    hcomp (λ z → λ { (t = i0) → base
                   ; (t = i1) → hcomp (λ l → λ { (i = i0) (z = i0) → loops base j
                                               ; (i = i1) (z = i0) → loops base j
                                               ; (j = i0) → hcomp (λ _ → λ { (i = i0) → base
                                                                           ; (i = i1) → base
                                                                           ; (k = i0) → loops base i
                                                                           ; (k = i1) → loops base i
                                                                           ; (z = i0) → loops base i
                                                                           })
                                                                  (loops base i)
                                               ; (j = i1) → hcomp (λ _ → λ { (i = i0) → base
                                                                           ; (i = i1) → base
                                                                           ; (k = i0) → loops base i
                                                                           ; (k = i1) → loops base i
                                                                           ; (z = i0) → loops base i
                                                                           })
                                                                  (loops base i)
                                               ; (k = i0) → hcomp (λ m → λ { (i = i0) → loops base (~ m ∨ j)
                                                                           ; (i = i1) → loops base (m ∧ j)
                                                                           ; (j = i0) → loops base (~ m ∨ i)
                                                                           ; (j = i1) → loops base (m ∧ i)
                                                                           ; (l = i0) → triv m i j
                                                                           })
                                                                  base
                                               ; (k = i1) → loops (loops base i) j
                                               })
                                      (loops (hcomp (λ _ → λ { (i = i0) → base
                                                             ; (i = i1) → base
                                                             ; (k = i0) → loops base i
                                                             ; (k = i1) → loops base i
                                                             ; (z = i0) → loops base i
                                                             })
                                                    (loops base i))
                                             j)
                   ; (i = i0) → hcomp (λ _ → λ { (t = i1) (j = i0) → base
                                               ; (t = i0) → base
                                               ; (j = i1) → base
                                               ; (k = i0) → loops base (~ t ∨ j)
                                               ; (k = i1) → loops base (~ t ∨ j)
                                               ; (z = i0) → loops base (~ t ∨ j)
                                               })
                                      (loops base (~ t ∨ j))
                   ; (i = i1) → hcomp (λ _ → λ { (t = i0) → base
                                               ; (j = i0) → base
                                               ; (t = i1) (j = i1) → base
                                               ; (k = i0) → loops base (t ∧ j)
                                               ; (k = i1) → loops base (t ∧ j)
                                               ; (z = i0) → loops base (t ∧ j)
                                               })
                                      (loops base (t ∧ j))
                   ; (j = i0) → hcomp (λ _ → λ { (t = i1) (i = i0) → base
                                               ; (t = i0) → base
                                               ; (i = i1) → base
                                               ; (k = i0) → loops base (~ t ∨ i)
                                               ; (k = i1) → loops base (~ t ∨ i)
                                               ; (z = i0) → loops base (~ t ∨ i)
                                               })
                                      (loops base (~ t ∨ i))
                   ; (j = i1) → hcomp (λ _ → λ { (t = i0) → base
                                               ; (i = i0) → base
                                               ; (t = i1) (i = i1) → base
                                               ; (k = i0) → loops base (t ∧ i)
                                               ; (k = i1) → loops base (t ∧ i)
                                               ; (z = i0) → loops base (t ∧ i)
                                               })
                                      (loops base (t ∧ i))
                   ; (k = i0) → hcomp (λ k → λ { (i = i0) → loops base (~ k ∨ ~ t ∨ j)
                                               ; (i = i1) → loops base (k ∧ t ∧ j)
                                               ; (j = i0) → loops base (~ k ∨ ~ t ∨ i)
                                               ; (j = i1) → loops base (k ∧ t ∧ i)
                                               ; (t = i0) → base
                                               })
                                      base
                   ; (k = i1) → triv t i j
                   })
          (lol3 t i j k)

goal : X ≃ S¹
goal = isoToEquiv (iso φ ψ φψ ψφ)
