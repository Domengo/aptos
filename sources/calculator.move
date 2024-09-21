// module metaschool::calculator_l05
// {
//     use std::string::{String,utf8};
//     use std::signer;

//     struct Message has key
//     {
//         my_message : String
//     }

//     public entry fun create_message(account: &signer)
//     {
//         if (!exists<Message>(signer::address_of(account))){
//             let message = Message {
//                 my_message : utf8(b"Hi, it's my first dApp on the Aptos ecosystem")
//             };
//             move_to(account,message);
//         }
//     }

//     public fun get_message(account: &signer): String acquires Message {
//         let calculator = borrow_global<Message>(signer::address_of(account));
//         calculator.my_message
//     }
// }

module metaschool::calculator_l05 {
    use std::string::{String, utf8};
    use std::signer;
    use std::debug;

    struct Message has key {
        my_message: String
    }

    struct Calculator has drop, key {
        result: u64
    }

    // // Passing the signer address to the function
    // public entry fun create_calculator(account: &signer) {
	//     // Defined the Calculator instance
	//     let calculator = Calculator { result: 0 };
	//     // Published the Calculator instance to the account provided
	//     move_to(account, calculator);
    // }

    	// Function acquires the Calculator resource
    public entry fun create_calculator(account: &signer) acquires Calculator {
    
			  // We check if the signer address already has a Calculator resource
			  // associated to it
        if (exists<Calculator>(signer::address_of(account))){
        
		        // Here, we are using borrow_global_mut to fetch the Calculator resource
		        // associated with the signer address
            let calculator = borrow_global_mut<Calculator>(signer::address_of(account));
            calculator.result = 0;
        }
        else {
        
	        // If no Calculator resource is present for the input signer address
	        // then we create a new instance of a resource
	        let calculator = Calculator { result: 0 };
	        move_to(account, calculator);
        }
    }

    public entry fun sign(s: &signer) {
        let addr = signer::address_of(s);
        debug::print(&addr);
    }

    /// Function to create a new message if it doesn't already exist
    public entry fun create_message(account: &signer) {
        if (!exists<Message>(signer::address_of(account))) {
            let message = Message {
                my_message: utf8(b"Hi, it's my first dApp on the Aptos ecosystemmm")
            };
            move_to(account, message);
        }
    }

    /// Function to update the message if it already exists
    public entry fun update_message(account: &signer, new_message: String) acquires Message {
        if (exists<Message>(signer::address_of(account))) {
            let message_ref = borrow_global_mut<Message>(signer::address_of(account));
            message_ref.my_message = new_message;
        } else {
            // Optional: Handle case where the message doesn't exist yet
            create_message(account);
        }
    }

    /// Function to get the message
    public fun get_message(account: &signer): String acquires Message {
        let message = borrow_global<Message>(signer::address_of(account));
        message.my_message
    }
}
