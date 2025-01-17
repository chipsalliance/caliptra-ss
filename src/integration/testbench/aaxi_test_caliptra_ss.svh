/* Class aaxi_test_caliptra_ss
 *      extends aaxi_test_base. */

import aaxi_pkg::*;
import aaxi_pkg_test::*;
import aaxi_pkg_xactor::*;

class aaxi_test_caliptra_ss extends aaxi_test_base;
    // Additional Slave BFMs slave5, slave6
    // slave0, slave1, slave2, slave3 and slave4 are defined in aaxi_test_base
    aaxi_device_class slave5, slave6, slave7, slave8;

    // Constructor to initialize the class 
    function new(string name); 
        super.new(name); // Call the parent class constructor 
        
        // Initialize and add new slave BFMs to the array 
        //slave5 = new(); 
        //slave6 = new(); 
        //slv_bfms.push_back(slave5); 
        //slv_bfms.push_back(slave6); 
    endfunction 
   /* 
    // Override bfm_param_setup to include new slaves 
    function void bfm_param_setup(); 
        super.bfm_param_setup(); // Call the base class method 
        
        // Setup parameters for additional slaves 
        aaxi_slave_param slv_par3; 
        
        slv_par3 = new($psprintf("slv_param%0d", slv_bfms.size() - 2));  
        slave5.cfg_info.copy_slave_param(slv_par3); 
        slv_param_Q.push_back(slv_par3); 
        
        slv_par3 = new($psprintf("slv_param%0d", slv_bfms.size() - 1)); 
        slave6.cfg_info.copy_slave_param(slv_par3); 
        slv_param_Q.push_back(slv_par3); 
    endfunction
    */
endclass
