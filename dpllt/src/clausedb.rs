use crate::bools::*;
use bitfield::bitfield;

bitfield! {
    pub struct ClauseHeader(u32);
    impl Debug;
    pub get_mark, set_mark :1, 0;
    pub get_learnt, set_learnt :2;
    pub get_extra_data, set_extra_data :3;
    pub get_reloced, set_reloced :4;
    pub get_size, set_size :31, 5;
}

pub type ClauseHeaderOffset = i32;
pub const CLAUSE_NONE: ClauseHeaderOffset = -1;
pub const CLAUSE_THEORY_UNDEF: ClauseHeaderOffset = -2;
pub const CLAUSE_THEORY_REFERENCE: ClauseHeaderOffset = -3;

pub struct ClauseDatabase {
    pub clause_data: Vec<u32>,
    pub wasted: u32,
}

impl ClauseDatabase {
    pub fn relocate_clause(
        &mut self,
        cref: ClauseHeaderOffset,
        new_data: &mut Vec<u32>,
    ) -> ClauseHeaderOffset {
        let header = self.get_header(cref);
        if header.get_reloced() {
            return *self.get_relocated_address(cref);
        }

        // copy
        let size_in_u32 = 1 + header.get_size() as usize + header.get_extra_data() as usize;
        let new_addr = new_data.len() as ClauseHeaderOffset;
        new_data.extend(&self.clause_data[cref as usize..(cref as usize + size_in_u32)]);

        // mark the old clause
        self.get_header_mut(cref).set_reloced(true);
        *self.get_relocated_address(cref) = new_addr;

        // return new address
        new_addr
    }

    pub fn update_size(&mut self, cref: ClauseHeaderOffset, new_size: usize) {
        let mut header = self.get_header(cref);
        if header.get_extra_data() {
            let activity_addr = self.get_activity_address(cref);
            self.clause_data[cref as usize + 1 + new_size] = self.clause_data[activity_addr];
        }
        header.set_size(new_size as u32);
        *self.get_header_mut(cref) = header;
    }

    pub fn free(&mut self, cref: ClauseHeaderOffset) {
        let header = self.get_header(cref);
        self.wasted += 1 + header.get_size() + header.get_extra_data() as u32;
    }

    pub fn add_clause(&mut self, lits: &[Lit], learnt: bool) -> ClauseHeaderOffset {
        let data_size = lits.len();

        let mut header = ClauseHeader(0);
        header.set_size(data_size as u32);
        header.set_learnt(learnt);
        header.set_extra_data(learnt); // TODO or extra clause field for simplification
        let header = header;

        let cref = self.clause_data.len() as i32;
        self.clause_data
            .push(unsafe { std::mem::transmute::<ClauseHeader, u32>(header) });
        self.clause_data.extend(unsafe {
            std::mem::transmute::<&[Lit],&[u32]>(lits)
        });

        if learnt {
            self.clause_data
                .push(unsafe { std::mem::transmute::<f32, u32>(0.0) });
        }

        cref
    }

    pub fn get_activity_address(&self, header_addr: ClauseHeaderOffset) -> usize {
        let header = self.get_header(header_addr);
        assert!(header.get_extra_data());
        assert!(header.get_learnt());

        header_addr as usize + 1 + header.get_size() as usize
    }

    pub fn get_activity<'a>(&'a self, header_addr: ClauseHeaderOffset) -> &'a f32 {
        let addr = self.get_activity_address(header_addr);
        unsafe { std::mem::transmute(&self.clause_data[addr]) }
    }

    pub fn get_activity_mut<'a>(&'a mut self, header_addr: ClauseHeaderOffset) -> &'a mut f32 {
        let header = self.get_header(header_addr);
        assert!(header.get_extra_data());
        assert!(header.get_learnt());
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut f32)
                //.offset((1 + header.get_size()) as isize * std::mem::size_of::<u32>() as isize);
                .offset(1 + header.get_size() as isize);
            &mut *ptr
        }
    }

    pub fn get_clause<'a>(
        &'a self,
        header_addr: ClauseHeaderOffset,
    ) -> (&'a ClauseHeader, &'a [Lit]) {
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = &self.clause_data[header_addr as usize];
        let header = unsafe { std::mem::transmute::<&u32, &ClauseHeader>(val) };
        let size = header.get_size() as usize;
        let lits = unsafe {
            let ptr = (self.clause_data.get(header_addr as usize).unwrap() as *const u32
                as *const  Lit)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            std::slice::from_raw_parts(ptr, size)
        };
        (header, lits)
    }

    pub fn get_clause_mut<'a>(
        &'a mut self,
        header_addr: ClauseHeaderOffset,
    ) -> (&'a mut ClauseHeader, &'a mut [Lit]) {
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = &mut self.clause_data[header_addr as usize];
        let header = unsafe { std::mem::transmute::<&mut u32, &mut ClauseHeader>(val) };
        let size = header.get_size() as usize;
        let lits = unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut Lit)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            std::slice::from_raw_parts_mut(ptr, size)
        };
        (header, lits)
    }

    pub fn get_header_mut<'a>(&'a mut self, header_addr: ClauseHeaderOffset) -> &'a mut ClauseHeader {
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = &mut self.clause_data[header_addr as usize];
        unsafe { std::mem::transmute::<&mut u32, &mut ClauseHeader>(val) }
    }

    pub fn get_header(&self, header_addr: ClauseHeaderOffset) -> ClauseHeader {
        //info!("get header {}/{}", header_addr, self.clause_data.len());
        assert!(header_addr >= 0);
        assert_eq!(
            std::mem::size_of::<ClauseHeader>(),
            std::mem::size_of::<u32>()
        );
        let val = self.clause_data[header_addr as usize];
        let h = unsafe { std::mem::transmute::<u32, ClauseHeader>(val) };
        //println!("Header {:?}", h);
        h
    }

    pub fn get_lits<'a>(&'a self, header_addr: ClauseHeaderOffset, size: usize) -> &'a [Lit] {
        //println!("getting lits from {}..+{}", header_addr, size);
        //let offset = std::mem::size_of::<ClauseHeader>() as isize;
        //println!("offset {:?}", offset);
        unsafe {
            let ptr =
                (&self.clause_data[header_addr as usize] as *const u32 as *const Lit).offset(1);
            std::slice::from_raw_parts(ptr, size)
        }
    }

    pub fn get_relocated_address<'a>(
        &'a mut self,
        header_addr: ClauseHeaderOffset,
    ) -> &mut ClauseHeaderOffset {
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut ClauseHeaderOffset)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            &mut *ptr
        }
    }

    pub fn get_lits_mut<'a>(
        &'a mut self,
        header_addr: ClauseHeaderOffset,
        size: usize,
    ) -> &'a mut [Lit] {
        unsafe {
            let ptr = (self.clause_data.get_mut(header_addr as usize).unwrap() as *mut u32
                as *mut Lit)
                //.offset(std::mem::size_of::<ClauseHeader>() as isize);
                .offset(1); //std::mem::size_of::<ClauseHeader>() as isize);
            std::slice::from_raw_parts_mut(ptr, size)
        }
    }
}

