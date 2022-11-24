# linked_list
Implementation of a linked list in Rust, closely following [Learning Rust With Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/index.html)
As can be seen in that book, a linked list is almost never what you want as a data structure.

But it's an interesting exercise to implement in unsafe Rust!

# Usage
This project uses the [just command runner](https://github.com/casey/just), which is configured to run normal and \
miri tests in a watcher process. `cargo-watch` and `miri` must be installed for this:
```
just test
just miri
```
