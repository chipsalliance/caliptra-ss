
//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// 
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************
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
