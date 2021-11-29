
################################################################
# This is a generated script based on design: rr_pcim_pchk_interconnect
#
# Though there are limitations about the generated script,
# the main purpose of this utility is to make learning
# IP Integrator Tcl commands easier.
################################################################

namespace eval _tcl {
proc get_script_folder {} {
   set script_path [file normalize [info script]]
   set script_folder [file dirname $script_path]
   return $script_folder
}
}
variable script_folder
set script_folder [_tcl::get_script_folder]

################################################################
# Check if script is running in correct Vivado version.
################################################################
set scripts_vivado_version 2020.2
set current_vivado_version [version -short]

if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
   puts ""
   catch {common::send_gid_msg -ssname BD::TCL -id 2041 -severity "ERROR" "This script was generated using Vivado <$scripts_vivado_version> and is being run in <$current_vivado_version> of Vivado. Please run the script in Vivado <$scripts_vivado_version> then open the design in Vivado <$current_vivado_version>. Upgrade the design by running \"Tools => Report => Report IP Status...\", then run write_bd_tcl to create an updated script."}

   return 1
}

################################################################
# START
################################################################

# To test this script, run the following commands from Vivado Tcl console:
# source rr_pcim_pchk_interconnect_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./myproj/project_1.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { $list_projs eq "" } {
   create_project project_1 myproj -part xcvu9p-flgb2104-2-i
}


# CHANGE DESIGN NAME HERE
variable design_name
set design_name rr_pcim_pchk_interconnect

# This script was generated for a remote BD. To create a non-remote design,
# change the variable <run_remote_bd_flow> to <0>.

set run_remote_bd_flow 1
if { $run_remote_bd_flow == 1 } {
  # Set the reference directory for source file relative paths (by default 
  # the value is script directory path)
  set origin_dir ./ip

  # Use origin directory path location variable, if specified in the tcl shell
  if { [info exists ::origin_dir_loc] } {
     set origin_dir $::origin_dir_loc
  }

  set str_bd_folder [file normalize ${origin_dir}]
  set str_bd_filepath ${str_bd_folder}/${design_name}/${design_name}.bd

  # Check if remote design exists on disk
  if { [file exists $str_bd_filepath ] == 1 } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2030 -severity "ERROR" "The remote BD file path <$str_bd_filepath> already exists!"}
     common::send_gid_msg -ssname BD::TCL -id 2031 -severity "INFO" "To create a non-remote BD, change the variable <run_remote_bd_flow> to <0>."
     common::send_gid_msg -ssname BD::TCL -id 2032 -severity "INFO" "Also make sure there is no design <$design_name> existing in your current project."

     return 1
  }

  # Check if design exists in memory
  set list_existing_designs [get_bd_designs -quiet $design_name]
  if { $list_existing_designs ne "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2033 -severity "ERROR" "The design <$design_name> already exists in this project! Will not create the remote BD <$design_name> at the folder <$str_bd_folder>."}

     common::send_gid_msg -ssname BD::TCL -id 2034 -severity "INFO" "To create a non-remote BD, change the variable <run_remote_bd_flow> to <0> or please set a different value to variable <design_name>."

     return 1
  }

  # Check if design exists on disk within project
  set list_existing_designs [get_files -quiet */${design_name}.bd]
  if { $list_existing_designs ne "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2035 -severity "ERROR" "The design <$design_name> already exists in this project at location:
    $list_existing_designs"}
     catch {common::send_gid_msg -ssname BD::TCL -id 2036 -severity "ERROR" "Will not create the remote BD <$design_name> at the folder <$str_bd_folder>."}

     common::send_gid_msg -ssname BD::TCL -id 2037 -severity "INFO" "To create a non-remote BD, change the variable <run_remote_bd_flow> to <0> or please set a different value to variable <design_name>."

     return 1
  }

  # Now can create the remote BD
  # NOTE - usage of <-dir> will create <$str_bd_folder/$design_name/$design_name.bd>
  create_bd_design -dir $str_bd_folder $design_name
} else {

  # Create regular design
  if { [catch {create_bd_design $design_name} errmsg] } {
     common::send_gid_msg -ssname BD::TCL -id 2038 -severity "INFO" "Please set a different value to variable <design_name>."

     return 1
  }
}

current_bd_design $design_name

##################################################################
# DESIGN PROCs
##################################################################


# Hierarchical cell: s02_couplers
proc create_hier_cell_s02_couplers { parentCell nameHier } {

  variable script_folder

  if { $parentCell eq "" || $nameHier eq "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2092 -severity "ERROR" "create_hier_cell_s02_couplers() - Empty argument(s)!"}
     return
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj

  # Create cell and set as current instance
  set hier_obj [create_bd_cell -type hier $nameHier]
  current_bd_instance $hier_obj

  # Create interface pins
  create_bd_intf_pin -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S_AXI


  # Create pins
  create_bd_pin -dir I -type clk M_ACLK
  create_bd_pin -dir I -type rst M_ARESETN
  create_bd_pin -dir I -type clk S_ACLK
  create_bd_pin -dir I -type rst S_ARESETN

  # Create instance: s02_regslice, and set properties
  set s02_regslice [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_register_slice:2.1 s02_regslice ]

  # Create interface connections
  connect_bd_intf_net -intf_net s02_couplers_to_s02_regslice [get_bd_intf_pins S_AXI] [get_bd_intf_pins s02_regslice/S_AXI]
  connect_bd_intf_net -intf_net s02_regslice_to_s02_couplers [get_bd_intf_pins M_AXI] [get_bd_intf_pins s02_regslice/M_AXI]

  # Create port connections
  connect_bd_net -net S_ACLK_1 [get_bd_pins S_ACLK] [get_bd_pins s02_regslice/aclk]
  connect_bd_net -net S_ARESETN_1 [get_bd_pins S_ARESETN] [get_bd_pins s02_regslice/aresetn]

  # Restore current instance
  current_bd_instance $oldCurInst
}

# Hierarchical cell: s01_couplers
proc create_hier_cell_s01_couplers { parentCell nameHier } {

  variable script_folder

  if { $parentCell eq "" || $nameHier eq "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2092 -severity "ERROR" "create_hier_cell_s01_couplers() - Empty argument(s)!"}
     return
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj

  # Create cell and set as current instance
  set hier_obj [create_bd_cell -type hier $nameHier]
  current_bd_instance $hier_obj

  # Create interface pins
  create_bd_intf_pin -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S_AXI


  # Create pins
  create_bd_pin -dir I -type clk M_ACLK
  create_bd_pin -dir I -type rst M_ARESETN
  create_bd_pin -dir I -type clk S_ACLK
  create_bd_pin -dir I -type rst S_ARESETN

  # Create instance: s01_regslice, and set properties
  set s01_regslice [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_register_slice:2.1 s01_regslice ]

  # Create interface connections
  connect_bd_intf_net -intf_net s01_couplers_to_s01_regslice [get_bd_intf_pins S_AXI] [get_bd_intf_pins s01_regslice/S_AXI]
  connect_bd_intf_net -intf_net s01_regslice_to_s01_couplers [get_bd_intf_pins M_AXI] [get_bd_intf_pins s01_regslice/M_AXI]

  # Create port connections
  connect_bd_net -net S_ACLK_1 [get_bd_pins S_ACLK] [get_bd_pins s01_regslice/aclk]
  connect_bd_net -net S_ARESETN_1 [get_bd_pins S_ARESETN] [get_bd_pins s01_regslice/aresetn]

  # Restore current instance
  current_bd_instance $oldCurInst
}

# Hierarchical cell: s00_couplers
proc create_hier_cell_s00_couplers { parentCell nameHier } {

  variable script_folder

  if { $parentCell eq "" || $nameHier eq "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2092 -severity "ERROR" "create_hier_cell_s00_couplers() - Empty argument(s)!"}
     return
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj

  # Create cell and set as current instance
  set hier_obj [create_bd_cell -type hier $nameHier]
  current_bd_instance $hier_obj

  # Create interface pins
  create_bd_intf_pin -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S_AXI


  # Create pins
  create_bd_pin -dir I -type clk M_ACLK
  create_bd_pin -dir I -type rst M_ARESETN
  create_bd_pin -dir I -type clk S_ACLK
  create_bd_pin -dir I -type rst S_ARESETN

  # Create instance: s00_regslice, and set properties
  set s00_regslice [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_register_slice:2.1 s00_regslice ]

  # Create interface connections
  connect_bd_intf_net -intf_net s00_couplers_to_s00_regslice [get_bd_intf_pins S_AXI] [get_bd_intf_pins s00_regslice/S_AXI]
  connect_bd_intf_net -intf_net s00_regslice_to_s00_couplers [get_bd_intf_pins M_AXI] [get_bd_intf_pins s00_regslice/M_AXI]

  # Create port connections
  connect_bd_net -net S_ACLK_1 [get_bd_pins S_ACLK] [get_bd_pins s00_regslice/aclk]
  connect_bd_net -net S_ARESETN_1 [get_bd_pins S_ARESETN] [get_bd_pins s00_regslice/aresetn]

  # Restore current instance
  current_bd_instance $oldCurInst
}

# Hierarchical cell: m00_couplers
proc create_hier_cell_m00_couplers { parentCell nameHier } {

  variable script_folder

  if { $parentCell eq "" || $nameHier eq "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2092 -severity "ERROR" "create_hier_cell_m00_couplers() - Empty argument(s)!"}
     return
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj

  # Create cell and set as current instance
  set hier_obj [create_bd_cell -type hier $nameHier]
  current_bd_instance $hier_obj

  # Create interface pins
  create_bd_intf_pin -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S_AXI


  # Create pins
  create_bd_pin -dir I -type clk M_ACLK
  create_bd_pin -dir I -type rst M_ARESETN
  create_bd_pin -dir I -type clk S_ACLK
  create_bd_pin -dir I -type rst S_ARESETN

  # Create instance: m00_regslice, and set properties
  set m00_regslice [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_register_slice:2.1 m00_regslice ]

  # Create interface connections
  connect_bd_intf_net -intf_net m00_couplers_to_m00_regslice [get_bd_intf_pins S_AXI] [get_bd_intf_pins m00_regslice/S_AXI]
  connect_bd_intf_net -intf_net m00_regslice_to_m00_couplers [get_bd_intf_pins M_AXI] [get_bd_intf_pins m00_regslice/M_AXI]

  # Create port connections
  connect_bd_net -net M_ACLK_1 [get_bd_pins M_ACLK] [get_bd_pins m00_regslice/aclk]
  connect_bd_net -net M_ARESETN_1 [get_bd_pins M_ARESETN] [get_bd_pins m00_regslice/aresetn]

  # Restore current instance
  current_bd_instance $oldCurInst
}

# Hierarchical cell: rr_pcim_pchk_interconnect
proc create_hier_cell_rr_pcim_pchk_interconnect_1 { parentCell nameHier } {

  variable script_folder

  if { $parentCell eq "" || $nameHier eq "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2092 -severity "ERROR" "create_hier_cell_rr_pcim_pchk_interconnect_1() - Empty argument(s)!"}
     return
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj

  # Create cell and set as current instance
  set hier_obj [create_bd_cell -type hier $nameHier]
  current_bd_instance $hier_obj

  # Create interface pins
  create_bd_intf_pin -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M00_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S00_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S01_AXI

  create_bd_intf_pin -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S02_AXI


  # Create pins
  create_bd_pin -dir I -type clk ACLK
  create_bd_pin -dir I -type rst ARESETN
  create_bd_pin -dir I -type clk M00_ACLK
  create_bd_pin -dir I -type rst M00_ARESETN
  create_bd_pin -dir I -type clk S00_ACLK
  create_bd_pin -dir I -type rst S00_ARESETN
  create_bd_pin -dir I -type clk S01_ACLK
  create_bd_pin -dir I -type rst S01_ARESETN
  create_bd_pin -dir I -type clk S02_ACLK
  create_bd_pin -dir I -type rst S02_ARESETN
  create_bd_pin -dir O m00_pc_asserted
  create_bd_pin -dir O -from 159 -to 0 m00_pc_status
  create_bd_pin -dir O s00_pc_asserted
  create_bd_pin -dir O -from 159 -to 0 s00_pc_status
  create_bd_pin -dir O s01_pc_asserted
  create_bd_pin -dir O -from 159 -to 0 s01_pc_status
  create_bd_pin -dir O s02_pc_asserted
  create_bd_pin -dir O -from 159 -to 0 s02_pc_status

  # Create instance: m00_couplers
  create_hier_cell_m00_couplers $hier_obj m00_couplers

  # Create instance: m00_pchk, and set properties
  set m00_pchk [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_protocol_checker:2.0 m00_pchk ]
  set_property -dict [ list \
   CONFIG.MAX_AR_WAITS {0} \
   CONFIG.MAX_AW_WAITS {0} \
   CONFIG.MAX_B_WAITS {0} \
   CONFIG.MAX_RD_BURSTS {32} \
   CONFIG.MAX_R_WAITS {0} \
   CONFIG.MAX_WR_BURSTS {32} \
   CONFIG.MAX_W_WAITS {0} \
 ] $m00_pchk

  # Create instance: s00_couplers
  create_hier_cell_s00_couplers $hier_obj s00_couplers

  # Create instance: s00_pchk, and set properties
  set s00_pchk [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_protocol_checker:2.0 s00_pchk ]
  set_property -dict [ list \
   CONFIG.MAX_AR_WAITS {0} \
   CONFIG.MAX_AW_WAITS {0} \
   CONFIG.MAX_B_WAITS {0} \
   CONFIG.MAX_RD_BURSTS {32} \
   CONFIG.MAX_R_WAITS {0} \
   CONFIG.MAX_WR_BURSTS {32} \
   CONFIG.MAX_W_WAITS {0} \
 ] $s00_pchk

  # Create instance: s01_couplers
  create_hier_cell_s01_couplers $hier_obj s01_couplers

  # Create instance: s01_pchk, and set properties
  set s01_pchk [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_protocol_checker:2.0 s01_pchk ]
  set_property -dict [ list \
   CONFIG.MAX_AR_WAITS {0} \
   CONFIG.MAX_AW_WAITS {0} \
   CONFIG.MAX_B_WAITS {0} \
   CONFIG.MAX_RD_BURSTS {32} \
   CONFIG.MAX_R_WAITS {0} \
   CONFIG.MAX_WR_BURSTS {32} \
   CONFIG.MAX_W_WAITS {0} \
 ] $s01_pchk

  # Create instance: s02_couplers
  create_hier_cell_s02_couplers $hier_obj s02_couplers

  # Create instance: s02_pchk, and set properties
  set s02_pchk [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_protocol_checker:2.0 s02_pchk ]
  set_property -dict [ list \
   CONFIG.MAX_AR_WAITS {0} \
   CONFIG.MAX_AW_WAITS {0} \
   CONFIG.MAX_B_WAITS {0} \
   CONFIG.MAX_RD_BURSTS {32} \
   CONFIG.MAX_R_WAITS {0} \
   CONFIG.MAX_WR_BURSTS {32} \
   CONFIG.MAX_W_WAITS {0} \
 ] $s02_pchk

  # Create instance: xbar, and set properties
  set xbar [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_crossbar:2.1 xbar ]
  set_property -dict [ list \
   CONFIG.NUM_MI {1} \
   CONFIG.NUM_SI {3} \
   CONFIG.S00_ARB_PRIORITY {1} \
   CONFIG.S01_ARB_PRIORITY {1} \
   CONFIG.S02_ARB_PRIORITY {0} \
   CONFIG.STRATEGY {0} \
 ] $xbar

  # Create interface connections
  connect_bd_intf_net -intf_net m00_couplers_to_rr_pcim_pchk_interconnect [get_bd_intf_pins M00_AXI] [get_bd_intf_pins m00_couplers/M_AXI]
  connect_bd_intf_net -intf_net [get_bd_intf_nets m00_couplers_to_rr_pcim_pchk_interconnect] [get_bd_intf_pins M00_AXI] [get_bd_intf_pins m00_pchk/PC_AXI]
  set_property HDL_ATTRIBUTE.MARK_DEBUG {true} [get_bd_intf_nets m00_couplers_to_rr_pcim_pchk_interconnect]
  connect_bd_intf_net -intf_net rr_pcim_pchk_interconnect_to_s00_couplers [get_bd_intf_pins S00_AXI] [get_bd_intf_pins s00_couplers/S_AXI]
  connect_bd_intf_net -intf_net [get_bd_intf_nets rr_pcim_pchk_interconnect_to_s00_couplers] [get_bd_intf_pins S00_AXI] [get_bd_intf_pins s00_pchk/PC_AXI]
  set_property HDL_ATTRIBUTE.MARK_DEBUG {true} [get_bd_intf_nets rr_pcim_pchk_interconnect_to_s00_couplers]
  connect_bd_intf_net -intf_net rr_pcim_pchk_interconnect_to_s01_couplers [get_bd_intf_pins S01_AXI] [get_bd_intf_pins s01_couplers/S_AXI]
  connect_bd_intf_net -intf_net [get_bd_intf_nets rr_pcim_pchk_interconnect_to_s01_couplers] [get_bd_intf_pins S01_AXI] [get_bd_intf_pins s01_pchk/PC_AXI]
  set_property HDL_ATTRIBUTE.MARK_DEBUG {true} [get_bd_intf_nets rr_pcim_pchk_interconnect_to_s01_couplers]
  connect_bd_intf_net -intf_net rr_pcim_pchk_interconnect_to_s02_couplers [get_bd_intf_pins S02_AXI] [get_bd_intf_pins s02_couplers/S_AXI]
  connect_bd_intf_net -intf_net [get_bd_intf_nets rr_pcim_pchk_interconnect_to_s02_couplers] [get_bd_intf_pins S02_AXI] [get_bd_intf_pins s02_pchk/PC_AXI]
  set_property HDL_ATTRIBUTE.MARK_DEBUG {true} [get_bd_intf_nets rr_pcim_pchk_interconnect_to_s02_couplers]
  connect_bd_intf_net -intf_net s00_couplers_to_xbar [get_bd_intf_pins s00_couplers/M_AXI] [get_bd_intf_pins xbar/S00_AXI]
  connect_bd_intf_net -intf_net s01_couplers_to_xbar [get_bd_intf_pins s01_couplers/M_AXI] [get_bd_intf_pins xbar/S01_AXI]
  connect_bd_intf_net -intf_net s02_couplers_to_xbar [get_bd_intf_pins s02_couplers/M_AXI] [get_bd_intf_pins xbar/S02_AXI]
  connect_bd_intf_net -intf_net xbar_to_m00_couplers [get_bd_intf_pins m00_couplers/S_AXI] [get_bd_intf_pins xbar/M00_AXI]

  # Create port connections
  connect_bd_net -net m00_pchk_pc_asserted [get_bd_pins m00_pc_asserted] [get_bd_pins m00_pchk/pc_asserted]
  connect_bd_net -net m00_pchk_pc_status [get_bd_pins m00_pc_status] [get_bd_pins m00_pchk/pc_status]
  connect_bd_net -net rr_pcim_pchk_interconnect_ACLK_net [get_bd_pins ACLK] [get_bd_pins m00_couplers/M_ACLK] [get_bd_pins m00_couplers/S_ACLK] [get_bd_pins m00_pchk/aclk] [get_bd_pins s00_couplers/M_ACLK] [get_bd_pins s00_couplers/S_ACLK] [get_bd_pins s00_pchk/aclk] [get_bd_pins s01_couplers/M_ACLK] [get_bd_pins s01_couplers/S_ACLK] [get_bd_pins s01_pchk/aclk] [get_bd_pins s02_couplers/M_ACLK] [get_bd_pins s02_couplers/S_ACLK] [get_bd_pins s02_pchk/aclk] [get_bd_pins xbar/aclk]
  connect_bd_net -net rr_pcim_pchk_interconnect_ARESETN_net [get_bd_pins ARESETN] [get_bd_pins m00_couplers/M_ARESETN] [get_bd_pins m00_couplers/S_ARESETN] [get_bd_pins m00_pchk/aresetn] [get_bd_pins s00_couplers/M_ARESETN] [get_bd_pins s00_couplers/S_ARESETN] [get_bd_pins s00_pchk/aresetn] [get_bd_pins s01_couplers/M_ARESETN] [get_bd_pins s01_couplers/S_ARESETN] [get_bd_pins s01_pchk/aresetn] [get_bd_pins s02_couplers/M_ARESETN] [get_bd_pins s02_couplers/S_ARESETN] [get_bd_pins s02_pchk/aresetn] [get_bd_pins xbar/aresetn]
  set_property HDL_ATTRIBUTE.MARK_DEBUG {true} [get_bd_nets rr_pcim_pchk_interconnect_ARESETN_net]
  connect_bd_net -net s00_pchk_pc_asserted [get_bd_pins s00_pc_asserted] [get_bd_pins s00_pchk/pc_asserted]
  connect_bd_net -net s00_pchk_pc_status [get_bd_pins s00_pc_status] [get_bd_pins s00_pchk/pc_status]
  connect_bd_net -net s01_pchk_pc_asserted [get_bd_pins s01_pc_asserted] [get_bd_pins s01_pchk/pc_asserted]
  connect_bd_net -net s01_pchk_pc_status [get_bd_pins s01_pc_status] [get_bd_pins s01_pchk/pc_status]
  connect_bd_net -net s02_pchk_pc_asserted [get_bd_pins s02_pc_asserted] [get_bd_pins s02_pchk/pc_asserted]
  connect_bd_net -net s02_pchk_pc_status [get_bd_pins s02_pc_status] [get_bd_pins s02_pchk/pc_status]

  # Restore current instance
  current_bd_instance $oldCurInst
}


# Procedure to create entire design; Provide argument to make
# procedure reusable. If parentCell is "", will use root.
proc create_root_design { parentCell } {

  variable script_folder
  variable design_name

  if { $parentCell eq "" } {
     set parentCell [get_bd_cells /]
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2090 -severity "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_gid_msg -ssname BD::TCL -id 2091 -severity "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj


  # Create interface ports
  set M00_AXI [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M00_AXI ]
  set_property -dict [ list \
   CONFIG.ADDR_WIDTH {64} \
   CONFIG.DATA_WIDTH {512} \
   CONFIG.FREQ_HZ {250000000} \
   CONFIG.NUM_READ_OUTSTANDING {32} \
   CONFIG.NUM_WRITE_OUTSTANDING {32} \
   CONFIG.PROTOCOL {AXI4} \
   ] $M00_AXI
  set_property APERTURES {{0x0 16E}} [get_bd_intf_ports M00_AXI]

  set S00_AXI [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S00_AXI ]
  set_property -dict [ list \
   CONFIG.ADDR_WIDTH {64} \
   CONFIG.ARUSER_WIDTH {0} \
   CONFIG.AWUSER_WIDTH {0} \
   CONFIG.BUSER_WIDTH {0} \
   CONFIG.DATA_WIDTH {512} \
   CONFIG.FREQ_HZ {250000000} \
   CONFIG.HAS_BRESP {1} \
   CONFIG.HAS_BURST {1} \
   CONFIG.HAS_CACHE {1} \
   CONFIG.HAS_LOCK {1} \
   CONFIG.HAS_PROT {1} \
   CONFIG.HAS_QOS {1} \
   CONFIG.HAS_REGION {1} \
   CONFIG.HAS_RRESP {1} \
   CONFIG.HAS_WSTRB {1} \
   CONFIG.ID_WIDTH {14} \
   CONFIG.MAX_BURST_LENGTH {256} \
   CONFIG.NUM_READ_OUTSTANDING {32} \
   CONFIG.NUM_READ_THREADS {16} \
   CONFIG.NUM_WRITE_OUTSTANDING {32} \
   CONFIG.NUM_WRITE_THREADS {16} \
   CONFIG.PROTOCOL {AXI4} \
   CONFIG.READ_WRITE_MODE {READ_WRITE} \
   CONFIG.RUSER_BITS_PER_BYTE {0} \
   CONFIG.RUSER_WIDTH {0} \
   CONFIG.SUPPORTS_NARROW_BURST {1} \
   CONFIG.WUSER_BITS_PER_BYTE {0} \
   CONFIG.WUSER_WIDTH {0} \
   ] $S00_AXI
  set_property APERTURES {{0x0 16E}} [get_bd_intf_ports S00_AXI]

  set S01_AXI [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S01_AXI ]
  set_property -dict [ list \
   CONFIG.ADDR_WIDTH {64} \
   CONFIG.ARUSER_WIDTH {0} \
   CONFIG.AWUSER_WIDTH {0} \
   CONFIG.BUSER_WIDTH {0} \
   CONFIG.DATA_WIDTH {512} \
   CONFIG.FREQ_HZ {250000000} \
   CONFIG.HAS_BRESP {1} \
   CONFIG.HAS_BURST {1} \
   CONFIG.HAS_CACHE {1} \
   CONFIG.HAS_LOCK {1} \
   CONFIG.HAS_PROT {1} \
   CONFIG.HAS_QOS {1} \
   CONFIG.HAS_REGION {1} \
   CONFIG.HAS_RRESP {1} \
   CONFIG.HAS_WSTRB {1} \
   CONFIG.ID_WIDTH {14} \
   CONFIG.MAX_BURST_LENGTH {256} \
   CONFIG.NUM_READ_OUTSTANDING {32} \
   CONFIG.NUM_READ_THREADS {16} \
   CONFIG.NUM_WRITE_OUTSTANDING {32} \
   CONFIG.NUM_WRITE_THREADS {16} \
   CONFIG.PROTOCOL {AXI4} \
   CONFIG.READ_WRITE_MODE {READ_WRITE} \
   CONFIG.RUSER_BITS_PER_BYTE {0} \
   CONFIG.RUSER_WIDTH {0} \
   CONFIG.SUPPORTS_NARROW_BURST {1} \
   CONFIG.WUSER_BITS_PER_BYTE {0} \
   CONFIG.WUSER_WIDTH {0} \
   ] $S01_AXI
  set_property APERTURES {{0x0 16E}} [get_bd_intf_ports S01_AXI]

  set S02_AXI [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S02_AXI ]
  set_property -dict [ list \
   CONFIG.ADDR_WIDTH {64} \
   CONFIG.ARUSER_WIDTH {0} \
   CONFIG.AWUSER_WIDTH {0} \
   CONFIG.BUSER_WIDTH {0} \
   CONFIG.DATA_WIDTH {512} \
   CONFIG.FREQ_HZ {250000000} \
   CONFIG.HAS_BRESP {1} \
   CONFIG.HAS_BURST {1} \
   CONFIG.HAS_CACHE {1} \
   CONFIG.HAS_LOCK {1} \
   CONFIG.HAS_PROT {1} \
   CONFIG.HAS_QOS {1} \
   CONFIG.HAS_REGION {1} \
   CONFIG.HAS_RRESP {1} \
   CONFIG.HAS_WSTRB {1} \
   CONFIG.ID_WIDTH {14} \
   CONFIG.MAX_BURST_LENGTH {256} \
   CONFIG.NUM_READ_OUTSTANDING {32} \
   CONFIG.NUM_READ_THREADS {16} \
   CONFIG.NUM_WRITE_OUTSTANDING {32} \
   CONFIG.NUM_WRITE_THREADS {16} \
   CONFIG.PROTOCOL {AXI4} \
   CONFIG.READ_WRITE_MODE {READ_WRITE} \
   CONFIG.RUSER_BITS_PER_BYTE {0} \
   CONFIG.RUSER_WIDTH {0} \
   CONFIG.SUPPORTS_NARROW_BURST {1} \
   CONFIG.WUSER_BITS_PER_BYTE {0} \
   CONFIG.WUSER_WIDTH {0} \
   ] $S02_AXI
  set_property APERTURES {{0x0 16E}} [get_bd_intf_ports S02_AXI]


  # Create ports
  set ACLK [ create_bd_port -dir I -type clk -freq_hz 250000000 ACLK ]
  set_property -dict [ list \
   CONFIG.ASSOCIATED_BUSIF {S00_AXI:M00_AXI:S01_AXI:S02_AXI} \
 ] $ACLK
  set ARESETN [ create_bd_port -dir I -type rst ARESETN ]
  set m00_pc_asserted [ create_bd_port -dir O m00_pc_asserted ]
  set m00_pc_status [ create_bd_port -dir O -from 159 -to 0 m00_pc_status ]
  set s00_pc_asserted [ create_bd_port -dir O s00_pc_asserted ]
  set s00_pc_status [ create_bd_port -dir O -from 159 -to 0 s00_pc_status ]
  set s01_pc_asserted [ create_bd_port -dir O s01_pc_asserted ]
  set s01_pc_status [ create_bd_port -dir O -from 159 -to 0 s01_pc_status ]
  set s02_pc_asserted [ create_bd_port -dir O s02_pc_asserted ]
  set s02_pc_status [ create_bd_port -dir O -from 159 -to 0 s02_pc_status ]

  # Create instance: rr_pcim_pchk_interconnect
  create_hier_cell_rr_pcim_pchk_interconnect_1 [current_bd_instance .] rr_pcim_pchk_interconnect

  # Create interface connections
  connect_bd_intf_net -intf_net S00_AXI_1 [get_bd_intf_ports S00_AXI] [get_bd_intf_pins rr_pcim_pchk_interconnect/S00_AXI]
  connect_bd_intf_net -intf_net S01_AXI_1 [get_bd_intf_ports S01_AXI] [get_bd_intf_pins rr_pcim_pchk_interconnect/S01_AXI]
  connect_bd_intf_net -intf_net S02_AXI_1 [get_bd_intf_ports S02_AXI] [get_bd_intf_pins rr_pcim_pchk_interconnect/S02_AXI]
  connect_bd_intf_net -intf_net axi_interconnect_0_M00_AXI [get_bd_intf_ports M00_AXI] [get_bd_intf_pins rr_pcim_pchk_interconnect/M00_AXI]

  # Create port connections
  connect_bd_net -net ACLK_1 [get_bd_ports ACLK] [get_bd_pins rr_pcim_pchk_interconnect/ACLK] [get_bd_pins rr_pcim_pchk_interconnect/M00_ACLK] [get_bd_pins rr_pcim_pchk_interconnect/S00_ACLK] [get_bd_pins rr_pcim_pchk_interconnect/S01_ACLK] [get_bd_pins rr_pcim_pchk_interconnect/S02_ACLK]
  connect_bd_net -net ARESETN_1 [get_bd_ports ARESETN] [get_bd_pins rr_pcim_pchk_interconnect/ARESETN] [get_bd_pins rr_pcim_pchk_interconnect/M00_ARESETN] [get_bd_pins rr_pcim_pchk_interconnect/S00_ARESETN] [get_bd_pins rr_pcim_pchk_interconnect/S01_ARESETN] [get_bd_pins rr_pcim_pchk_interconnect/S02_ARESETN]
  connect_bd_net -net rr_pcim_pchk_interconnect_m00_pc_asserted [get_bd_ports m00_pc_asserted] [get_bd_pins rr_pcim_pchk_interconnect/m00_pc_asserted]
  connect_bd_net -net rr_pcim_pchk_interconnect_m00_pc_status [get_bd_ports m00_pc_status] [get_bd_pins rr_pcim_pchk_interconnect/m00_pc_status]
  connect_bd_net -net rr_pcim_pchk_interconnect_s00_pc_asserted [get_bd_ports s00_pc_asserted] [get_bd_pins rr_pcim_pchk_interconnect/s00_pc_asserted]
  connect_bd_net -net rr_pcim_pchk_interconnect_s00_pc_status [get_bd_ports s00_pc_status] [get_bd_pins rr_pcim_pchk_interconnect/s00_pc_status]
  connect_bd_net -net rr_pcim_pchk_interconnect_s01_pc_asserted [get_bd_ports s01_pc_asserted] [get_bd_pins rr_pcim_pchk_interconnect/s01_pc_asserted]
  connect_bd_net -net rr_pcim_pchk_interconnect_s01_pc_status [get_bd_ports s01_pc_status] [get_bd_pins rr_pcim_pchk_interconnect/s01_pc_status]
  connect_bd_net -net rr_pcim_pchk_interconnect_s02_pc_asserted [get_bd_ports s02_pc_asserted] [get_bd_pins rr_pcim_pchk_interconnect/s02_pc_asserted]
  connect_bd_net -net rr_pcim_pchk_interconnect_s02_pc_status [get_bd_ports s02_pc_status] [get_bd_pins rr_pcim_pchk_interconnect/s02_pc_status]

  # Create address segments
  assign_bd_address -offset 0x00000000 -range 0x00010000000000000000 -target_address_space [get_bd_addr_spaces S00_AXI] [get_bd_addr_segs M00_AXI/Reg] -force
  assign_bd_address -offset 0x00000000 -range 0x00010000000000000000 -target_address_space [get_bd_addr_spaces S01_AXI] [get_bd_addr_segs M00_AXI/Reg] -force
  assign_bd_address -offset 0x00000000 -range 0x00010000000000000000 -target_address_space [get_bd_addr_spaces S02_AXI] [get_bd_addr_segs M00_AXI/Reg] -force


  # Restore current instance
  current_bd_instance $oldCurInst

  validate_bd_design
  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


