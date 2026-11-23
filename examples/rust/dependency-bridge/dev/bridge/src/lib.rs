pub struct Device { pub n: u64 }
pub fn open() -> Result<Device, String> { Ok(Device { n: 7 }) }
