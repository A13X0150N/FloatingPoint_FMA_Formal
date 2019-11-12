# Define clocks
netlist clock clk -period 10 

# Constraints
formal netlist constraint float_0_busy_in 1'b0
formal netlist constraint float_1_busy_in 1'b0
