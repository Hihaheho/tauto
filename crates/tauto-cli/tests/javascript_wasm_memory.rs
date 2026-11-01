//! Run this file under Miri as well as the ordinary native test runner.
//! It exercises the same arena source embedded in generated Wasm modules.
#![allow(dead_code, clippy::mut_from_ref)]
mod arena {
    include!("../src/javascript/wasm_runtime.rs");
    fn dispatch(_: u32, _: &Value) -> Value {
        unreachable!()
    }
    fn access_value(_: u32, _: u32, _: &Value) -> Value {
        unreachable!()
    }

    #[test]
    fn mutable_view_keeps_its_owner_alive() {
        let owner = store(vec![10_i64, 20], "vector");
        let frame = Frame::default();
        let value = frame.write::<Vec<i64>>(&owner);
        let child = unsafe { view(&mut value[0] as *mut i64, true, 0, false, &frame) };
        drop(frame);
        release(owner["handle"].as_u64().unwrap() as u32);
        {
            let frame = Frame::default();
            *frame.write::<i64>(&child) += 2;
        }
        {
            let frame = Frame::default();
            assert_eq!(*frame.read::<i64>(&child), 12);
        }
        release(child["handle"].as_u64().unwrap() as u32);
        assert!(HANDLES.with(|h| h.borrow().is_empty()));
    }
    #[test]
    fn a_handle_past_u32_is_refused_not_cut_to_another() {
        let owner = store(vec![10_i64], "vector");
        let id = owner["handle"].as_u64().unwrap();
        let wide = json!({ "handle": id + (1_u64 << 32) });
        let refused = std::panic::catch_unwind(|| handle_id(&wide));
        assert!(refused.is_err());
        release(id as u32);
    }
    #[test]
    fn nested_loans_unlock_in_reverse_order() {
        let owner = store(vec![1_i64, 2], "vector");
        let frame = Frame::default();
        let data = frame.write::<Vec<i64>>(&owner);
        let slice = unsafe { view(data.as_mut_slice() as *mut [i64], true, 0, false, &frame) };
        drop(frame);
        let frame = Frame::default();
        let data = frame.slice_mut::<i64>(&slice);
        let element = unsafe { view(&mut data[1] as *mut i64, true, 0, false, &frame) };
        drop(frame);
        release(slice["handle"].as_u64().unwrap() as u32);
        {
            let frame = Frame::default();
            *frame.write::<i64>(&element) = 42;
        }
        release(element["handle"].as_u64().unwrap() as u32);
        assert_eq!(take::<Vec<i64>>(&owner, &Frame::default()), vec![1, 42]);
    }
    #[test]
    fn multiple_shared_views_do_not_invalidate_each_other() {
        let owner = store(String::from("hello"), "text");
        let frame = Frame::default();
        let a = frame.read::<String>(&owner);
        let first = unsafe { view(a as *const String as *mut String, false, 0, false, &frame) };
        let b = frame.read::<String>(&owner);
        let second = unsafe { view(b as *const String as *mut String, false, 0, false, &frame) };
        drop(frame);
        release(first["handle"].as_u64().unwrap() as u32);
        {
            let frame = Frame::default();
            assert_eq!(frame.read::<String>(&second), "hello");
        }
        release(second["handle"].as_u64().unwrap() as u32);
        assert_eq!(take::<String>(&owner, &Frame::default()), "hello");
    }
    #[test]
    fn callback_scope_retires_transitive_stack_views() {
        let mut stack_value = 7_i64;
        let scoped = Frame::scoped();
        let view = unsafe { view(&mut stack_value as *mut i64, true, 0, false, &scoped) };
        let frame = Frame::default();
        let x = frame.write::<i64>(&view);
        let child = unsafe { self::view(x as *mut i64, true, 0, false, &frame) };
        drop(frame);
        drop(scoped);
        assert!(HANDLES.with(|h| {
            !h.borrow()
                .contains_key(&(child["handle"].as_u64().unwrap() as u32))
        }));
        stack_value = 9;
        assert_eq!(stack_value, 9);
    }
    #[test]
    fn erased_iterator_lifetime_is_backed_by_its_parent_loan() {
        struct Cursor<'a>(std::slice::Iter<'a, i64>);
        let owner = store(vec![10_i64, 20], "vector");
        let frame = Frame::default();
        let cursor = Cursor(frame.read::<Vec<i64>>(&owner).iter());
        let cursor: Cursor<'static> = unsafe { std::mem::transmute(cursor) };
        let id = insert(Box::new(cursor), frame.loans.borrow().clone(), true);
        let cursor = json!({"handle":id});
        drop(frame);
        release(owner["handle"].as_u64().unwrap() as u32);
        let frame = Frame::default();
        let value = frame.write::<Cursor<'static>>(&cursor).0.next().unwrap();
        let item = unsafe { view(value as *const i64 as *mut i64, false, 0, false, &frame) };
        drop(frame);
        release(id);
        {
            let frame = Frame::default();
            assert_eq!(*frame.read::<i64>(&item), 10);
        }
        release(item["handle"].as_u64().unwrap() as u32);
        assert!(HANDLES.with(|h| h.borrow().is_empty()));
    }
}
