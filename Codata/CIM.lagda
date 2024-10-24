\begin{code}
{-# OPTIONS --safe #-}

open import Prelude
open import Algebra

open import Path.Reasoning

module Codata.CIM where

private variable X : Type

module _ (M M̅ : Type → Type)
  (mon : Monad M)
  (fnc : Functor M̅)
  where

  open Monad mon
  open Functor fnc

  μ : M (M A) → M A
  μ xs = xs >>= id

  η = return

  M[_] : (A → B) → M A → M B
  M[_] = mmap

  M̅[_] : (A → B) → M̅ A → M̅ B
  M̅[_] = map

  μ∘η : μ ∘ η {A = M A} ≡ id
  μ∘η = funExt (>>=-idˡ _)

  η∘Mμ : μ ∘ M[ η {A = A} ] ≡ id
  η∘Mμ = funExt λ x → >>=-assoc x _ _ ; cong (x >>=_) (funExt λ x′ → >>=-idˡ _ (η x′)) ; >>=-idʳ x

  η∘f : (f : A → B) → η ∘ f ≡ M[ f ] ∘ η
  η∘f f = funExt λ x → sym (>>=-idˡ _ _)

  f∘μ : (f : A → B) → μ ∘ M[ M[ f ] ] ≡ M[ f ] ∘ μ
  f∘μ f = funExt λ x → >>=-assoc x _ _ ; cong (x >>=_) (funExt (λ x′ → >>=-idˡ _ _)) ; sym (>>=-assoc x _ _)

  μ-assoc : μ ∘ μ ≡ μ ∘ M[ μ { A = A } ]
  μ-assoc = funExt λ x → >>=-assoc x _ _ ; cong (x >>=_) (funExt λ x′ → sym (>>=-idˡ _ _)) ; sym (>>=-assoc x _ _)

  M[]-comp : (f : B → C) (g : A → B) → M[ f ] ∘ M[ g ] ≡ M[ f ∘ g ]
  M[]-comp f g = funExt (mmap-comp f g)

  μ-M : (f : A → M (M B)) → μ ∘ μ ∘ M[ f ] ≡ μ ∘ M[ μ ∘ f ]
  μ-M f =
    μ ∘ μ ∘ M[ f ] ≡⟨ cong (_∘ M[ f ]) μ-assoc ⟩
    μ ∘ M[ μ ] ∘ M[ f ] ≡⟨ cong (μ ∘_) (M[]-comp μ f) ⟩
    μ ∘ M[ μ ∘ f ] ∎
    
  record Module : Type₁ where
    field
      μ′ : M̅ (M A) → M̅ A
      μ-η : μ′ ∘ M̅[ η ] ≡ id {A = M̅ A}
      μ-μ : μ′ ∘ μ′ {A = M A} ≡ μ′ ∘ M̅[ μ ]

  record Ideal : Type₁ where
    field
      mod : Module
    open Module mod public
    field
      σ : M̅ A → M A
      hom : μ ∘ σ ≡ σ ∘ μ′ {A = A}
      natural : (f : A → B) → σ ∘ M̅[ f ] ≡ M[ f ] ∘ σ

  Equation : Type → Type → Type
\end{code}
%<*equation>
\begin{code}
  Equation X A = X → M (X ⊎ A)
\end{code}
%</equation>
\begin{code}
  Solution : Type → Type → Type
\end{code}
%<*soln>
\begin{code}
  Solution X A = X → M A
\end{code}
%</soln>
\begin{code}

  infix 4 _Solves_
\end{code}
%<*solves>
\begin{code}
  _Solves_ : Solution X A → Equation X A → Type
  e† Solves e = e† ≡ μ ∘ M[ e† ▿ η ] ∘ e
\end{code}
%</solves>
\begin{code}

  Flat : Type → Type → Type
\end{code}
%<*flat>
\begin{code}
  Flat X A = X → M̅ (X ⊎ A) ⊎ A
\end{code}
%</flat>
\begin{code}

  record CIM : Type₁ where
    field ideal : Ideal
    open Ideal ideal public

    infixl 30 _‡
    field
\end{code}
%<*solve>
\begin{code}
      _‡ : Flat X A → Solution X A
\end{code}
%</solve>
%<*solution>
\begin{code}
      solution :  (eᵢ : Flat X A) →
                  eᵢ ‡ Solves (σ ▿ η ∘ inr) ∘ eᵢ
\end{code}
%</solution>
\begin{code}
    Flatᵍ : Type → Type → Type
    Flatᵍ X A = X → M (M̅ X ⊎ A)

    module _ (eⱼ : Flatᵍ X A) where
      e : Equation X A
      e = μ ∘ M[ M[ inl ] ∘ σ ▿ η ∘ inr ] ∘ eⱼ

      ẽᵢ : Flat (M̅ X) A
      ẽᵢ = inl ∘ μ′ ∘ M̅[ eⱼ ]

      ẽ : Equation (M̅ X) A
      ẽ = (σ ▿ η ∘ inr) ∘ ẽᵢ

      _ : ẽ ≡ σ ∘ μ′ ∘ M̅[ eⱼ ]
      _ = refl

      ẽ† : Solution (M̅ X) A
      ẽ† = ẽᵢ ‡

      e† : Solution X A
      e† = μ ∘ M[ ẽ† ▿ η ] ∘ eⱼ

      lemma : μ ∘ M[ ẽ† ▿ η ] ∘ ẽ ≡ μ ∘ M[ e† ] ∘ σ
      lemma =
        μ ∘ M[ ẽ† ▿ η ] ∘ ẽ                     ≡⟨⟩
        μ ∘ M[ ẽ† ▿ η ] ∘ σ ∘ μ′ ∘ M̅[ eⱼ ]      ≡˘⟨ cong (λ s → μ ∘ M[ ẽ† ▿ η ] ∘ s ∘ M̅[ eⱼ ]) hom ⟩ 
        μ ∘ M[ ẽ† ▿ η ] ∘ μ ∘ σ ∘ M̅[ eⱼ ]       ≡⟨ cong (λ s → μ ∘ M[ ẽ† ▿ η ] ∘ μ ∘ s) (natural eⱼ) ⟩
        μ ∘ M[ ẽ† ▿ η ] ∘ μ ∘ M[ eⱼ ] ∘ σ       ≡˘⟨ cong (λ s → μ ∘ s ∘ M[ eⱼ ] ∘ σ) (f∘μ (ẽ† ▿ η) ) ⟩
        μ ∘ μ ∘ M[ M[ ẽ† ▿ η ] ] ∘ M[ eⱼ ] ∘ σ  ≡⟨ cong (λ s → μ ∘ μ ∘ s ∘ σ) (M[]-comp M[ ẽ† ▿ η ] eⱼ) ⟩
        μ ∘ μ ∘ M[ M[ ẽ† ▿ η ] ∘ eⱼ ] ∘ σ       ≡⟨ cong (_∘ σ) (μ-M _) ⟩
        μ ∘ M[ μ ∘ M[ ẽ† ▿ η ] ∘ eⱼ ] ∘ σ       ≡⟨⟩
        μ ∘ M[ e† ] ∘ σ ∎

      soln : e† Solves e
      soln =
        e†                                                                      ≡⟨⟩
        μ ∘ M[ ẽ† ▿ η ] ∘ eⱼ                                                    ≡⟨ cong (λ s → μ ∘ M[ s ▿ η ] ∘ eⱼ) (solution ẽᵢ) ⟩
        μ ∘ M[ μ ∘ M[ ẽ† ▿ η ] ∘ ẽ ▿ η ] ∘ eⱼ                                   ≡⟨ cong (λ s → μ ∘ M[ s ▿ η ] ∘ eⱼ) lemma ⟩
        μ ∘ M[ μ ∘ M[ e† ] ∘ σ ▿ η ] ∘ eⱼ                                       ≡˘⟨ cong (λ s → μ ∘ M[ μ ∘ M[ e† ] ∘ σ ▿ s ∘ η ] ∘ eⱼ ) μ∘η ⟩
        μ ∘ M[ μ ∘ M[ e† ] ∘ σ ▿ μ ∘ η ∘ η ] ∘ eⱼ                               ≡⟨ cong (λ s → μ ∘ M[ s ] ∘ eⱼ) (funExt (▿-fusion μ _ _)) ⟩
        μ ∘ M[ μ ∘ (M[ e† ] ∘ σ ▿ η ∘ η) ] ∘ eⱼ                                 ≡˘⟨ cong (_∘ eⱼ) (μ-M (M[ e† ] ∘ σ ▿ η ∘ η)) ⟩
        μ ∘ μ ∘ M[ M[ e† ] ∘ σ ▿ η ∘ η  ] ∘ eⱼ                                  ≡⟨⟩
        μ ∘ μ ∘ M[ M[ (e† ▿ η) ∘ inl ] ∘ σ ▿ η ∘ η ] ∘ eⱼ                       ≡˘⟨ cong (λ s → μ ∘ μ ∘ M[ s ∘ σ ▿ η ∘ η ] ∘ eⱼ) (M[]-comp (e† ▿ η) inl) ⟩
        μ ∘ μ ∘ M[ M[ e† ▿ η ] ∘ M[ inl ] ∘ σ ▿ η ∘ η ] ∘ eⱼ                    ≡⟨⟩
        μ ∘ μ ∘ M[ M[ e† ▿ η ] ∘ M[ inl ] ∘ σ ▿ η ∘ (e† ▿ η) ∘ inr ] ∘ eⱼ       ≡⟨ cong (λ s → μ ∘ μ ∘ M[ M[ e† ▿ η ] ∘ M[ inl ] ∘ σ ▿ s ∘ inr ] ∘ eⱼ) (η∘f (e† ▿ η)) ⟩
        μ ∘ μ ∘ M[ M[ e† ▿ η ] ∘ M[ inl ] ∘ σ ▿ M[ e† ▿ η ] ∘ η ∘ inr ] ∘ eⱼ    ≡⟨ cong (λ s → μ ∘ μ ∘ M[ s ] ∘ eⱼ) (funExt (▿-fusion M[ e† ▿ η ] _ _)) ⟩
        μ ∘ μ ∘ M[ M[ e† ▿ η ] ∘ (M[ inl ] ∘ σ ▿ η ∘ inr) ] ∘ eⱼ                ≡˘⟨ cong (λ s → μ ∘ μ ∘ s ∘ eⱼ) (M[]-comp M[ e† ▿ η ] (M[ inl ] ∘ σ ▿ η ∘ inr)) ⟩
        μ ∘ μ ∘ M[ M[ e† ▿ η ] ] ∘ M[ M[ inl ] ∘ σ ▿ η ∘ inr ] ∘ eⱼ             ≡⟨ cong (λ s → μ ∘ s ∘ M[ M[ inl ] ∘ σ ▿ η ∘ inr ] ∘ eⱼ) (f∘μ (e† ▿ η)) ⟩
        μ ∘ M[ e† ▿ η ] ∘ μ      ∘ M[ M[ inl ] ∘ σ ▿ η ∘ inr ] ∘ eⱼ             ≡⟨⟩
        μ ∘ M[ e† ▿ η ] ∘ e ∎
\end{code}
