/* The verifier's startup initializes the Lean runtime only.

   Lean's generated `main` calls `lean_initialize` whenever the program imports
   a module of the `Lean` package (here `Lean.Data.Json`). That initializes the
   whole Lean library — the elaborator, parser, tactics and kernel — about
   20 ms per run, none of which the verifier uses. The modules it does import
   are initialized by `initialize_verification_Main`, as for any program that
   uses no `Lean` module. This definition is linked before the Lean libraries
   (`moreLinkArgs` in lakefile.toml), so it replaces theirs. */
void lean_initialize_runtime_module(void);

void lean_initialize(void) { lean_initialize_runtime_module(); }
