//! Moved from `tauto_surface::bindings`: these read the standard library, which takes the reader.
#![allow(unused_imports)]

use std::collections::{HashMap, HashSet};
use tauto_surface::bindings::*;
use tauto_surface::bindings::*;
use tauto_surface::identity::*;
use tauto_surface::resolve::*;
use tauto_surface::surface::*;

#[test]
fn host_effects_keep_their_namespace_when_a_value_shares_the_spelling() {
    tauto_parse::install();
    for spelling in ["exceeded"] {
        let mut bindings = library_bindings();
        let effect = bindings.effect(spelling).unwrap().clone();
        assert_eq!(Some(&effect), bindings.get(spelling));
        let value = DeclRef::fresh(spelling);
        bindings.source_alias(spelling, value.clone());
        assert_eq!(bindings.get(spelling), Some(&value));
        assert_eq!(bindings.effect(spelling), Some(&effect));
    }
}

#[test]
fn a_copy_that_gives_a_library_spelling_a_new_meaning_hands_it_back() {
    tauto_parse::install();
    // Declaring a standard file on a copy aliases `Text` to the file's
    // own declaration: taking the copy in keeps that, as declaring the
    // file on the bindings themselves does.
    let mut bindings = library_bindings();
    let library = bindings.get("Text").unwrap().clone();
    let own = DeclRef::fresh("Text");
    let since = tauto_surface::identity::forked::next_generation();
    let mut copy = bindings.clone();
    copy.source_alias("Text", own.clone());
    let mut in_turn = bindings.clone();
    in_turn.source_alias("Text", own.clone());
    copy.subtract(since, &bindings);
    assert!(bindings.absorb(copy));
    assert_ne!(library, own);
    assert_eq!(bindings.get("Text"), Some(&own));
    assert_eq!(bindings.get("Text"), in_turn.get("Text"));
}

#[test]
fn a_copy_that_gives_a_constructor_spelling_a_new_choice_hands_it_back() {
    tauto_parse::install();
    let mut bindings = library_bindings();
    let library = bindings.choices("Finished").unwrap()[0].clone();
    let own = DeclRef::fresh("Finished");
    bindings.add_constructor(own.clone());
    let since = tauto_surface::identity::forked::next_generation();
    let mut copy = bindings.clone();
    copy.source_alias("Finished", own.clone());
    let mut in_turn = bindings.clone();
    in_turn.source_alias("Finished", own.clone());
    copy.subtract(since, &bindings);
    assert!(bindings.absorb(copy));
    assert_ne!(library, own);
    assert_eq!(bindings.choices("Finished"), Some(&vec![own]));
    assert_eq!(bindings.choices("Finished"), in_turn.choices("Finished"));
}

#[test]
fn copies_that_both_add_choices_to_a_spelling_keep_the_choices_of_each() {
    tauto_parse::install();
    // A spelling's choices are a set: what two files add side by side is
    // what they add in turn.
    let mut bindings = library_bindings();
    let (a, b): (Name, Name) = (
        DeclRef::fresh("Cancelled").into(),
        DeclRef::fresh("Cancelled").into(),
    );
    let mut in_turn = bindings.clone();
    in_turn.constructor_alias("Cancelled", &a);
    in_turn.constructor_alias("Cancelled", &b);
    let since = tauto_surface::identity::forked::next_generation();
    let mut first = bindings.clone();
    first.constructor_alias("Cancelled", &a);
    let mut second = bindings.clone();
    second.constructor_alias("Cancelled", &b);
    first.subtract(since, &bindings);
    second.subtract(since, &bindings);
    assert!(bindings.absorb(second));
    assert!(bindings.absorb(first));
    let sorted = |b: &Bindings| {
        let mut c = b.choices("Cancelled").cloned().unwrap();
        c.sort();
        c
    };
    assert_eq!(sorted(&bindings), sorted(&in_turn));
}

#[test]
fn a_library_type_keeps_its_identity_when_a_constructor_shares_its_name() {
    tauto_parse::install();
    let bindings = library_bindings();
    let family = bindings.get("Finished").unwrap();
    let constructor = &bindings.choices("Finished").unwrap()[0];
    assert_ne!(family, constructor);
    assert!(bindings.is_type(family));
    assert!(bindings.is_constructor_reference(constructor));
    assert_eq!(
        bindings.selection("Finished"),
        Some(constructor.clone().into())
    );
    assert!(bindings.type_constructor_selection("Finished").is_some());
}

#[test]
fn a_revision_retains_reservations_without_retaining_visibility() {
    tauto_parse::install();
    let mut first = library_bindings();
    let declaration = first.declare(&Name::from("module::value"));
    let mut next = first.next_revision();
    assert!(next.get("module::value").is_none());
    assert_eq!(next.declare(&Name::from("module::value")), declaration);
    assert_ne!(
        library_bindings().declare(&Name::from("module::value")),
        declaration
    );
    assert_eq!(first.get("module::value"), Some(&declaration));
}

#[test]
fn a_source_declaration_does_not_reuse_an_inherited_library_identity() {
    tauto_parse::install();
    let mut bindings = library_bindings();
    let inherited = bindings.get("List").unwrap().clone();
    let mut sibling = bindings.clone();
    let own = bindings.declare(&Name::from("List"));
    assert_ne!(own, inherited);
    assert_eq!(bindings.get("List"), Some(&own));
    assert_eq!(sibling.get("List"), Some(&inherited));
    assert_eq!(sibling.declare(&Name::from("List")), own);
    assert_eq!(bindings.declare(&Name::from("List")), own);
    assert!(!is_library(&Name::Global(own), "List"));
}

#[test]
fn declaring_a_bound_reference_retains_it_in_cloned_source_views() {
    tauto_parse::install();
    let mut bindings = library_bindings();
    let reference = DeclRef::fresh("module::value");
    bindings.declare(&Name::Global(reference.clone()));
    let mut copy = bindings.clone();
    assert_eq!(copy.declare(&Name::from("module::value")), reference);
}

#[test]
fn generated_declarations_keep_their_reserved_identity_when_defined() {
    tauto_parse::install();
    let mut bindings = library_bindings();
    let family: Name = bindings.declare(&Name::from("Family")).into();
    let generated = bindings.generated(&family, Generation::Equality);
    assert_eq!(
        bindings.declare(&Name::from(generated.display())),
        generated
    );
}

#[test]
fn effect_and_value_identities_survive_a_revision_separately() {
    tauto_parse::install();
    let mut bindings = library_bindings();
    let spelling = Name::from("answer");
    let effect = bindings.declare_effect(&spelling);
    let function = bindings.declare(&spelling);
    assert_ne!(effect, function);
    assert_eq!(bindings.effect("answer"), Some(&effect));
    assert_eq!(bindings.get("answer"), Some(&function));
    let mut revision = bindings.next_revision();
    assert_eq!(revision.declare_effect(&spelling), effect);
    assert_eq!(revision.declare(&spelling), function);
    assert_eq!(revision.effect("answer"), Some(&effect));
    let designated = library_name("fail");
    revision.declare(&Name::from("fail"));
    assert_eq!(revision.effect("fail"), designated.as_global());
}

#[test]
fn library_definitions_use_the_designated_references() {
    tauto_parse::install();
    let mut bindings = library_definition_bindings();
    for name in ["List", "Pair", "Nat", "SynIdent"] {
        assert_eq!(
            Name::Global(bindings.declare(&Name::from(name))),
            library_name(name)
        );
    }
}
