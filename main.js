/*
 * @licstart The following is the entire license notice for the
 * JavaScript code in this file.
 *
 * Decompression code adapted from UCL
 * Copyright (C) 1996-2002 Markus Franz Xaver Johannes Oberhumer
 *
 * jztool
 * Copyright (C) 2021 Aidan MacDonald
 *
 * jztool.js
 * Copyright (C) 2021 astrolabe
 * Copyright (C) 2022 Aidan MacDonald
 *
 * The JavaScript code in this file is free software: you can
 * redistribute it and/or modify it under the terms of the GNU
 * General Public License (GNU GPL) as published by the Free Software
 * Foundation, either version 2 of the License, or (at your option)
 * any later version.  The code is distributed WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU GPL for more details.
 *
 * @licend The above is the entire license notice for the JavaScript
 * code in this file.
 */

const VERSION = '0.1';

/* ============================================================================
 * UTILITIES
 * ========================================================================= */

function read_be32(buf, offset) {
    let ub = buf.buffer;
    if(ub.byteLength - offset < 4)
        throw new Error("buffer read out of bounds");

    return new DataView(ub).getUint32(offset, false);
}

function buf_eq(buf, offset, xbuf) {
    if(offset + xbuf.length > buf.length)
        return false;

    for(let ix = 0; ix < xbuf.length; ++ix)
        if(buf[offset + ix] !== xbuf[ix])
            return false;

    return true;
}

/* ============================================================================
 * UCL DECOMPRESSOR & UNPACKER
 * ========================================================================= */

function ucl_nrv2e_decompress(src) {
    let bit = 0;
    let ilen = 0;
    let last_m_off = 1;
    let dst = [];

    const E_INPUT_OVERRUN = "UCL: input overrun";
    const E_LOOKBEHIND_OVERRUN = "UCL: lookbehind overrun";

    function fail(cond, err) {
        if(cond)
            throw new Error(err);
    }

    function get_bit() {
        bit = bit & 0x7f ? (bit << 1) : (src[ilen++] << 1) + 1;
        return (bit >> 8) & 1;
    }

    while(true) {
        let m_off, m_len;

        while(get_bit()) {
            fail(ilen >= src.length, E_INPUT_OVERRUN);
            dst.push(src[ilen++]);
        }

        m_off = 1;
        while(true) {
            m_off = m_off*2 + get_bit();
            fail(ilen >= src.length, E_INPUT_OVERRUN);
            fail(m_off > 0xffffff + 3, E_LOOKBEHIND_OVERRUN);
            if(get_bit())
                break;
            m_off = (m_off - 1)*2 + get_bit();
        }

        if(m_off === 2) {
            m_off = last_m_off;
            m_len = get_bit();
        } else {
            fail(ilen >= src.length, E_INPUT_OVERRUN);
            m_off = (m_off - 3)*256 + src[ilen++];
            if(m_off === 0xffffffff)
                break;

            m_len = (m_off ^ 0xffffffff) & 1;
            m_off >>= 1;
            last_m_off = ++m_off;
        }

        if(m_len > 0)
            m_len = 1 + get_bit();
        else if(get_bit())
            m_len = 3 + get_bit();
        else {
            m_len++;
            do {
                m_len = m_len*2 + get_bit();
                fail(ilen >= src.length, E_INPUT_OVERRUN);
            } while(!get_bit());
            m_len += 3;
        }

        if(m_off > 0x500)
            m_len++;

        fail(m_off > dst.length, E_LOOKBEHIND_OVERRUN);

        let lb_off = dst.length - m_off;
        dst.push(dst[lb_off++]);

        for(let ix = 0; ix < m_len; ++ix)
            dst.push(dst[lb_off++]);
    }

    return dst;
}

function ucl_unpack(src){
    if(src.length < 18)
        throw new Error('UCL: input is too short for header');

    const magic = [0x00, 0xe9, 0x55, 0x43, 0x4c, 0xff, 0x01, 0x1a];
    const method = src[12];
    const block_size = read_be32(src, 14);

    if(!buf_eq(src, 0, magic))
        throw new Error('UCL: invalid magic');
    if(method !== 0x2e)
        throw new Error('UCL: unsupported method');
    if(block_size < 1024 || block_size > 8*1024*1024)
        throw new Error('UCL: invalid block size');

    let pos = 18;
    let dst = [];
    while(true) {
        const out_len = read_be32(src, pos);
        pos += 4;
        if(out_len === 0)
            break;
        if(src.length - pos < 4)
            throw new Error('UCL: unexpected EOF');

        const in_len = read_be32(src, pos);
        pos += 4;
        if(in_len > block_size || out_len > block_size || in_len === 0 || in_len > out_len)
            throw new Error('UCL: invalid lengths');
        if(src.length - pos < in_len)
            throw new Error('UCL: unexpected EOF');

        if(in_len < out_len) {
            const out = ucl_nrv2e_decompress(src.slice(pos, pos + in_len));
            if(out.length !== out_len)
                throw new Error('UCL: decompressed the incorrect amount');

            dst = dst.concat(out);
        } else {
            for(let ix = 0; ix < in_len; ix++)
                dst.push(src[pos + ix]);
        }

        pos += in_len;
    }

    return Uint8Array.from(dst);
}

/* ============================================================================
 * TAR FILE EXTRACTION
 * ========================================================================= */

function tar_extract(tar, filename) {
    const BLOCK_SIZE = 512;

    const NAME_OFF   = 0;   const NAME_LEN   = 100;
    const SIZE_OFF   = 124; const SIZE_LEN   = 12;
    const CHKSUM_OFF = 148; const CHKSUM_LEN = 8;
    const TYPE_OFF   = 156;

    const T_REG = 0x30; // regular file

    function read_str(buf, offset, max_length) {
        if(buf.length - offset < max_length)
            throw new Error("Tar: unexpected EOF");

        let s = "";
        for(let ix = 0; ix < max_length; ++ix) {
            const ch = buf[offset + ix];
            if(ch === 0)
                break;

            s += String.fromCharCode(ch);
        }

        return s;
    }

    function read_octal(buf, offset, max_length) {
        let n = 0;
        for(let ix = 0; ix < max_length; ix++) {
            const c = buf[offset + ix];
            if(c === 0)
                break;
            if(c < 0x30 || c > 0x37)
                throw new Error('Tar: invalid octal digit');

            n *= 8;
            n += c - 0x30;
        }

        return n;
    }

    function calc_checksum(buf, offset) {
        if(buf.length - offset < BLOCK_SIZE)
            throw new Error('Tar: unexpected EOF');

        const u32_max = 0xffffffff;
        let res = 256;

        for(let ix = 0; ix < CHKSUM_OFF; ++ix)
            res = (res + buf[offset + ix]) & u32_max;
        for(let ix = CHKSUM_OFF+CHKSUM_LEN; ix < BLOCK_SIZE; ++ix)
            res = (res + buf[offset + ix]) & u32_max;
        return res;
    }

    function read_header(buf, offset) {
        if(buf.length - offset < BLOCK_SIZE)
            throw new Error('Tar: unexpected EOF');

        // Assume end of archive if there is no checksum
        if(buf[offset + CHKSUM_OFF] === 0)
            return null;

        const checksum = read_octal(buf, offset + CHKSUM_OFF, CHKSUM_LEN);
        if(checksum !== calc_checksum(buf, offset))
            throw new Error('Tar: checksum mismatch at offset ' + offset);

        return {
            name: read_str(buf, offset + NAME_OFF, NAME_LEN),
            size: read_octal(buf, offset + SIZE_OFF, SIZE_LEN),
            type: buf[offset+TYPE_OFF] ? buf[offset+TYPE_OFF] : T_REG,
        };
    }

    let offset = 0;
    while(true) {
        const header = read_header(tar, offset);
        offset += BLOCK_SIZE;
        if(header === null)
            break;

        if(header.name === filename) {
            if(header.type !== T_REG)
                throw new Error('Tar: ' + filename + ' is not a regular file');

            return tar.slice(offset, offset + header.size);
        }

        offset += header.size;
        if((header.size % BLOCK_SIZE) !== 0)
            offset += BLOCK_SIZE - (header.size % BLOCK_SIZE);
    }

    throw new Error('Tar: file \'' + filename + '\' not found in archive');
}

/* ============================================================================
 * INGENIC USB BOOT PROTOCOL
 * ========================================================================= */

const CPU_X1000 = "x1000";

const CPU_INFO = {
    "x1000": {
        vendor_id: 0xa108,
        product_id: 0x1000,
    },
};

const VR_SET_DATA_ADDRESS = 1;
const VR_SET_DATA_LENGTH = 2;
const VR_FLUSH_CACHES = 3;
const VR_PROGRAM_START1 = 4;
const VR_PROGRAM_START2 = 5;

async function usb_vendor_req(device, request, argument){
    await device.controlTransferOut({
        requestType: 'vendor',
        recipient: 'device',
        request: request,
        value: argument >> 16,
        index: argument & 0xffff
    }, new Uint8Array(0));
}

async function usb_send(device, address, data){
    await usb_vendor_req(device, VR_SET_DATA_ADDRESS, address);
    await usb_vendor_req(device, VR_SET_DATA_LENGTH, data.length);
    await device.transferOut(1, data);
}

async function run_stage1(device, spl){
    await usb_send(device, 0xf4001000, spl);
    await usb_vendor_req(device, VR_PROGRAM_START1, 0xf4001800);
}

async function run_stage2(device, bootloader){
    await usb_send(device, 0x80004000, bootloader);
    await usb_vendor_req(device, VR_FLUSH_CACHES, 0);
    await usb_vendor_req(device, VR_PROGRAM_START2, 0x80004000);
}

/* ============================================================================
 * FRONTEND
 * ========================================================================= */

const PLAYER_INFO = {
    "m3k": {
        name: "FiiO M3K",
        file_ext: "m3k",
        boot_button: "Volume Down",
        cpu: CPU_X1000,
    },
    "q1": {
        name: "Shanling Q1",
        file_ext: "q1",
        boot_button: "Play",
        cpu: CPU_X1000,
    },
};

let bootloader_ab = null;
let spl_ab = null;

async function retrieve_file(file_name){
    let resp = await fetch(file_name);
    if(!resp.ok) throw new Error("Error retrieving file '" + file_name + "'");
    return new Uint8Array(await resp.arrayBuffer());
}

window.addEventListener('DOMContentLoaded', function(){
    const debug_console = document.getElementById('console');

    function get_player_info() {
        let elem = document.getElementById('select-player-model');
        let info = PLAYER_INFO[elem.value];
        if(info === undefined)
            throw new Error("Unknown player model: " + elem.value);

        return info;
    }

    function get_cpu_info() {
        let player_info = get_player_info();
        let cpu_info = CPU_INFO[player_info.cpu];
        if(cpu_info === undefined)
            throw new Error("Player has unknown CPU: " + player_info.cpu);

        return cpu_info;
    }

    function debug_log(item){
        debug_console.value += item + '\n';
    }

    function add_button(id, callback){
        const el = document.getElementById(id);

        el.addEventListener('click', function(){
            el.disabled = true;
            callback()
                .catch(function(e){
                    el.disabled = false;
                    debug_log(e);
                });
        });
    }

    add_button('button-select-player', async function(){
        const info = get_player_info();
        debug_log('Selected player: ' + info.name);

        let tar = await retrieve_file('bootloader.' + info.file_ext);
        spl_ab = tar_extract(tar, 'spl.' + info.file_ext);

        bootloader_ab = ucl_unpack(tar_extract(tar, 'bootloader.ucl'));
        let bootloader_version_ab = tar_extract(tar, 'bootloader-info.txt');
        let bootloader_version = new TextDecoder().decode(bootloader_version_ab).replace(/\n|\r/, '');

        debug_log('Bootloader files retrieved!');
        debug_log('Bootloader version: ' + bootloader_version);

        document.getElementById('select-player-model').disabled = true;
        document.getElementById('button-load').disabled = false;
        Array.from(document.getElementsByClassName('boot-button'))
            .forEach(x => x.innerText = info.boot_button);
    });

    add_button('button-load', async function(){
        if(navigator.usb === undefined){
            throw new Error('This browser does not support WebUSB');
        }

        if(bootloader_ab === null || spl_ab === null){
            throw new Error('Bootloader files not retrieved!');
        }

        const cpu_info = get_cpu_info();

        debug_log('Asking for device...');
        let device = await navigator.usb.requestDevice({
            filters: [{
                vendorId: cpu_info.vendor_id,
                productId: cpu_info.product_id
            }]
        });

        debug_log('Opening device...');
        await device.open();

        try{
            debug_log('Claiming device interface...');
            await device.claimInterface(0);

            debug_log('Loading stage1 (SPL)...');
            await run_stage1(device, spl_ab);

            debug_log('Pausing for SPL to come up...');
            await new Promise(x => setTimeout(x, 500));

            debug_log('Loading stage2 (bootloader)...');
            await run_stage2(device, bootloader_ab);

            debug_log('Closing device...');
            await device.close();

            debug_log('Done!');
        }
        catch(e){
            await device.close();
            throw e;
        }
    });

    debug_log('jztool.js ' + VERSION);
});
