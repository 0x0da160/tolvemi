//! Tolvemi（tlvm）の Python binding。`tlvm_core::embed`（crates/tlvm の `embed`） を薄く包む。
//!
//! 値の受け渡しは plain JSON（crates/tlvm の `plain` の対応表）を経由する。Python の値を `json.dumps` で文字列にし、
//! 結果を `json.loads` で戻すので、整数は桁数によらず Python の int として正確に往復する。

use pyo3::create_exception;
use pyo3::exceptions::PyException;
use pyo3::prelude::*;
use pyo3::types::PyList;
use tlvm_core::embed::{diagnostic_json, Diagnostic, Program as EmbedProgram, RunError};

create_exception!(tlvm, TlvmError, PyException, "tlvm の例外の基底クラス。");
create_exception!(tlvm, CompileError, TlvmError, "source が検査で拒否された。属性 diagnostics は診断の dict の list。");
create_exception!(tlvm, InputError, TlvmError, "入力を入力型の値として読めない。属性 diagnostics は診断の dict の list。");
create_exception!(tlvm, ResourceExhausted, TlvmError, "実行の資源上限を超えた。属性 kind、observed、limit。");
create_exception!(tlvm, HostAborted, TlvmError, "ホスト側の物理上限（評価の深さ）で中断した。属性 reason。");
create_exception!(tlvm, InternalError, TlvmError, "処理系の内部の失敗。属性 reason。");

/// 診断を一行 JSON にし、json.loads で dict にした list を作る。
fn diagnostics_list<'py>(py: Python<'py>, ds: &[Diagnostic]) -> PyResult<Bound<'py, PyList>> {
    let loads = py.import("json")?.getattr("loads")?;
    let items = ds.iter().map(|d| loads.call1((diagnostic_json(d),))).collect::<PyResult<Vec<_>>>()?;
    PyList::new(py, items)
}

fn with_diagnostics<'py>(py: Python<'py>, err: PyErr, ds: &[Diagnostic]) -> PyResult<PyErr> {
    err.value(py).setattr("diagnostics", diagnostics_list(py, ds)?)?;
    Ok(err)
}

fn summary(ds: &[Diagnostic]) -> String {
    ds.iter().map(|d| format!("{} {}", d.code, d.message)).collect::<Vec<_>>().join("; ")
}

fn run_error(py: Python<'_>, e: RunError) -> PyResult<PyErr> {
    Ok(match e {
        RunError::Input(ds) => with_diagnostics(py, InputError::new_err(summary(&ds)), &ds)?,
        RunError::ResourceExhausted { kind, observed, limit } => {
            let err = ResourceExhausted::new_err(format!("{kind} (observed {observed}, limit {limit})"));
            let v = err.value(py);
            v.setattr("kind", kind)?;
            v.setattr("observed", observed)?;
            v.setattr("limit", limit)?;
            err
        }
        RunError::HostAborted(r) => {
            let err = HostAborted::new_err(r.clone());
            err.value(py).setattr("reason", r)?;
            err
        }
        RunError::Internal(r) => {
            let err = InternalError::new_err(r.clone());
            err.value(py).setattr("reason", r)?;
            err
        }
    })
}

/// 検査済みのプログラム。`tlvm.compile` で作る。
#[pyclass(frozen, module = "tlvm")]
struct Program {
    inner: EmbedProgram,
}

#[pymethods]
impl Program {
    /// entry の関数名。
    #[getter]
    fn entry(&self) -> String {
        self.inner.entry().to_string()
    }

    /// entry の入力型（例：`List<Int>`）。
    #[getter]
    fn input_type(&self) -> String {
        self.inner.input_type()
    }

    /// entry の出力型。
    #[getter]
    fn output_type(&self) -> String {
        self.inner.output_type()
    }

    /// 受理時の warning（診断の dict の list）。
    #[getter]
    fn warnings<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        diagnostics_list(py, self.inner.warnings())
    }

    /// plain JSON の文字列を入力に実行し、plain JSON の文字列を返す。
    fn run_json(&self, py: Python<'_>, input: &str) -> PyResult<String> {
        let r = py.detach(|| self.inner.run_json(input));
        match r {
            Ok(out) => Ok(out),
            Err(e) => Err(run_error(py, e)?),
        }
    }

    /// Python の値を入力に実行し、Python の値を返す（json.dumps／json.loads で変換する）。
    fn run<'py>(&self, py: Python<'py>, value: &Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let json = py.import("json")?;
        let input: String = json.getattr("dumps")?.call1((value,))?.extract()?;
        let out = match py.detach(|| self.inner.run_json_exact(&input)) {
            Ok(out) => out,
            Err(e) => return Err(run_error(py, e)?),
        };
        json.getattr("loads")?.call1((out,))
    }

    fn __repr__(&self) -> String {
        format!("<tlvm.Program {}: {} -> {}>", self.inner.entry(), self.inner.input_type(), self.inner.output_type())
    }
}

/// source を検査する。拒否なら CompileError。
#[pyfunction]
fn compile(py: Python<'_>, source: &str) -> PyResult<Program> {
    match EmbedProgram::compile(source) {
        Ok(inner) => Ok(Program { inner }),
        Err(ds) => Err(with_diagnostics(py, CompileError::new_err(summary(&ds)), &ds)?),
    }
}

#[pymodule(name = "tlvm")]
fn tlvm_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = m.py();
    m.add_class::<Program>()?;
    m.add_function(wrap_pyfunction!(compile, m)?)?;
    m.add("TlvmError", py.get_type::<TlvmError>())?;
    m.add("CompileError", py.get_type::<CompileError>())?;
    m.add("InputError", py.get_type::<InputError>())?;
    m.add("ResourceExhausted", py.get_type::<ResourceExhausted>())?;
    m.add("HostAborted", py.get_type::<HostAborted>())?;
    m.add("InternalError", py.get_type::<InternalError>())?;
    Ok(())
}
