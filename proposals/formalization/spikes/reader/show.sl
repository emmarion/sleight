(def-fns _
  ((many show-form : (subterm many (Form) f) -> (many (Rope) r))
    (match many f _
      ((FAtom a) (RStr a))
      ((FList fs) (RCat (RStr "(") $ RCat (notail $ show-forms fs) $ RStr ")"))))
  ((many show-forms : (subterm many (List (Form)) fs) -> (many (Rope) r))
    (let-match many fs (Cons _ f rest) ((Nil _) (REmpty)))
    (let-match many rest (Cons _ _ _) ((Nil _) (tail $ show-form f)))
    (RCat (notail $ show-form f) $ RCat (RStr " ") $ notail $ show-forms rest)))

(def-fns _ $ (many show-read : (many (String) text) -> (many (String) s))
  (let-match many (read text) (Accepted _ fs _)
    ((Rejected _ m _)
      (match many m _
        ((MissingClose) "error: missing `)`")
        ((MissingCloseAfterDollar) "error: missing `)` after `$`")
        ((UnexpectedClose) "error: unexpected `)`"))))
  (let ((many s) (erased _)) (flatten $ show-forms fs))
  s)
