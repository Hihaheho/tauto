# The messages of the commands a project's totes give (`tauto NAME`).

# What joins two names in a list: "a and b".
commands-and = {" and "}
commands-trust-wrong-tote = trust.commands.{ $name } in Tauto.eure is for the tote { $tote }, which gives no command { $name }{ $givers }
# After the message above, the totes that do give the command.
commands-givers = {" "}({ $totes } does)
commands-ambiguous =
    the totes { $totes } each give a command { $name }; choose one in Tauto.eure:
    {"  "}{ $snippet }
commands-unread-dependencies =
    no command { $name }; these dependencies could not be read:
    {"  "}{ $unread }
commands-bad-trust = trust.commands.{ $name } in Tauto.eure: { $error }
commands-denied = the command { $name } of { $tote } needs { $kinds } to run; the host denies it by default
commands-denied-add = add to trust.commands.{ $name } in { $file }, naming only what it may use:
commands-denied-grant = grant it in { $file }, naming only what it may use:
commands-help-head = commands of the project in { $path }:
commands-help-not-read = {"  "}not read: { $item }
commands-state-built-in = not run: tauto has a built-in command of this name
commands-state-granted = granted { $kinds }
commands-state-granted-nothing = granted nothing
commands-state-other-tote = not run: another tote's command of this name is
commands-state-ambiguous = not run: several totes give it; choose one in trust.commands
commands-given-built-in = {" "}(not run: tauto has a built-in command of this name)
