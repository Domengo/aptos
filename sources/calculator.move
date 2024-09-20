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

    struct Message has key {
        my_message: String,
    }

    /// Function to create a new message if it doesn't already exist
    public entry fun create_message(account: &signer) {
        if (!exists<Message>(signer::address_of(account))) {
            let message = Message {
                my_message: utf8(b"Hi, it's my first dApp on the Aptos ecosystem"),
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
