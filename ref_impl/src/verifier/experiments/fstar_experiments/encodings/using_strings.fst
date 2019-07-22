module Using_strings

open FStar.String

let _ = assert_norm (length "" = 0)

let _ = assert_norm (strlen "" = 0)
