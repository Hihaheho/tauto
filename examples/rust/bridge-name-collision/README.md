`dev` declares `extern fn open` and answers it with its bridge crate. `other`,
another tote of the program, has a private `fn open`. The two share the bare
name, so `dev`'s extern is named in full (`dev::src::render::open`), but the
bridge crate's function is still `dev_bridge::open`: a name the program
happens to share elsewhere does not move it.
