%hide any
%hide (<|>)

data Chain : (Type -> Type) -> Type -> Type -> Type -> Type where
  MkChain : m (f -> a) -> g -> Chain m g f a

fin : Monad m => g -> Chain m g a a
fin = MkChain (pure id)

seq : Monad m =>      Chain m g g a -> m a
seq (MkChain m1 g) = map ($ g) m1

infixr 2 -:
(-:) : Monad m => m b -> Chain m g f a -> Chain m g (b -> f) a
(-:) m1 (MkChain m2 g) = MkChain (m1 >>= \b => m2 >>= \f_to_a => pure (\b_to_f => f_to_a (b_to_f b))) g

Parser : Type -> Type
(<|>) : Parser a -> Parser a -> Parser a
char : Char -> Parser ()
any : Parser Char

parameters {auto _ : Monad Parser}

  char_lit : Parser Char
  char_lit =

      seq {m=Parser} (char '"' -: char '\\' -: any -: char '"' -:
      fin             (\_, _, c, _ => c))

    <|>

      seq {m=Parser} (char '"' -:              any -: char '"' -:
      fin             (\_,    c, _ => c))
