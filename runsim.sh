xvlog func_vivado.v
xvlog sim_func.v
xelab -top sim_func -snapshot snapshot_func
xsim snapshot_func -R