module F = struct
  external cast : 'a -> 'b = "%identity"
  external blit_words : Obj.t -> int -> Obj.t -> int -> int -> unit = "caml_blit_bytes" [@@noalloc]
  let array_swap_imm a i x = let a = (cast a : int array) in let old = Array.unsafe_get a i in Array.unsafe_set a i (cast x : int); cast old
  let array_place_imm a i x = Array.unsafe_set (cast a : int array) i (cast x : int)
  let array_blit_imm src i dst j n = let w = Sys.word_size / 8 in blit_words (Obj.repr src) (i * w) (Obj.repr dst) (j * w) (n * w)
end
