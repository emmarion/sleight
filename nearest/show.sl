(def-fns _ $ (many unwords : (subterm many (List $ String) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (REmpty)))
  (RCat (RCat (RChar #\space) (RStr x)) $ notail $ unwords rest))

(def-fns _ $ (many show : (many (Nat) d) (many (List $ String) ties) -> (many (String) out))
  (let-match many ties (Cons _ _ _) ((Nil _) "no words\n"))
  (let ((many s) (erased _)) (flatten $ RCat (RCat (RStr (nat-str d)) (unwords ties)) (RChar #\newline)))
  s)
