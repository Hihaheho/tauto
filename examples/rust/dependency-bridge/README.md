`app` depends on `dev`, a tote whose extern `open` is answered by its bridge
crate, and on `util`, which declares another `open`. The two share the bare
name, so `dev`'s extern is named in full (`dev::src::render::open`); its
binding from `dev`'s bridge still applies.
