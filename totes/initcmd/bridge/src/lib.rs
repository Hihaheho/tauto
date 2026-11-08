//! What `tauto init` (`totes/initcmd`) still asks of Rust: the text of its
//! messages, in the user's language.

/// The message `key` of `tauto init`. `first` fills its one argument (`path`
/// or `error`); `init-cleanup-failed` takes the error in `first` and the
/// paths it could not clean up in `second`.
pub fn init_message(key: &str, first: &str, second: &str) -> String {
    let message = tauto_message::Message::new(key.to_string());
    let message = match key {
        "init-cleanup-failed" => message.arg("error", first).arg("paths", second),
        "init-failed" | "init-no-name" | "init-bad-name" | "init-bad-path" => {
            message.arg("error", first)
        }
        _ => message.arg("path", first),
    };
    tauto_messages::text(&message)
}
