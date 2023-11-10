import system.io

-- Define a custom data structure to store global state
structure GlobalState :=
(counter : ℕ := 0)

#check io.
-- Register an environment extension for the global state
def global_state_ext : environment → GlobalState :=
 GlobalState

-- Create a function to modify the global state
meta def modify_global_state (f : GlobalState → GlobalState) : io unit :=
do
  io.put_str_ln "Modifying global state...",
  old_env ← io.get_env,
  let new_env := old_env.modify_extension (λ _, f),
  io.set_env new_env

-- Access and modify the global state
def access_and_modify_global_state : io unit :=
do
  state ← io.run_tactic (io.run_command (pure ())),
  io.put_str_ln (to_string state),
  -- Modify the global state by incrementing the counter
  modify_global_state (λ gs, { gs with counter := gs.counter + 1 }),
  -- Access the modified global state
  modified_state ← io.run_tactic (io.run_command (pure ())),
  io.put_str_ln (to_string modified_state)

-- Run the IO action to access and modify the global state
def main : io unit :=
do
  io.put_str_ln "Accessing and modifying global state...",
  access_and_modify_global_state

-- Run the main IO action
#eval main
